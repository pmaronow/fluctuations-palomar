module
public import SKConstants.ParisiGrowingReplayDReference
public import SKConstants.BrownianDyadicGrid

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
open GaussianProposal

lemma measurePreserving_parisiGrowingReplay_matrix_spin {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    MeasurePreserving (fun a : ParisiGrowingReplaySpinStatic δ n q => (a.1.2.1,a.2))
      (parisiGrowingReplaySpinStaticLaw W δ n q)
      ((skDisorderLaw n).prod (Measure.pi (fun _ : Fin n => scalarHiddenPriorBool 0))) := by
  let A := (Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))).prod
    (Measure.infinitePi (fun j : ℕ => Measure.pi
      (fun _ : Fin n => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j))))
  have hW : MeasurePreserving (fun a : ScalarGrowingReplayStaticData δ n q => a.2.1)
      (scalarGrowingReplayStaticLaw W δ n q) (skDisorderLaw n) :=
    (measurePreserving_fst (μ := skDisorderLaw n) (ν := paperCompletionNoiseLaw n q)).comp
      (measurePreserving_snd (μ := A) (ν := (skDisorderLaw n).prod (paperCompletionNoiseLaw n q)))
  exact hW.prod (MeasurePreserving.id _)

lemma parisiGrowingReplay_density_matrix_spin_marginal {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ)
    (μ : Measure (ParisiGrowingReplaySpinStatic δ n q × (Fin n → Ω)))
    (hmarg : μ.map Prod.fst = parisiGrowingReplaySpinStaticLaw W δ n q) :
    μ.map (fun u => (u.1.1.2.1,u.1.2)) =
      (skDisorderLaw n).prod (Measure.pi (fun _ : Fin n => scalarHiddenPriorBool 0)) := by
  have hMP := measurePreserving_parisiGrowingReplay_matrix_spin W δ n q
  change μ.map ((fun a : ParisiGrowingReplaySpinStatic δ n q => (a.1.2.1,a.2)) ∘ Prod.fst) = _
  rw [← Measure.map_map hMP.measurable measurable_fst,hmarg]
  exact hMP.map_eq

theorem actualParisiGrowingReplayGaussianReference_exists {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (T : ℝ≥0) :
    ∃ I : ParisiGrowingReplaySpinStatic δ (ranks+q) q × (Fin (ranks+q) → Ω) → ℝ,
      MemLp I 2 ((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law))) ∧
      Integrable (brownianVectorContinuousExponential W.B
        (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) T I)
        ((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
          (Measure.pi (fun _ : Fin (ranks+q) => W.law))) ∧
      IsProbabilityMeasure (((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law))).withDensity (fun u => ENNReal.ofReal
          (brownianVectorContinuousExponential W.B
            (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) T I u))) ∧
      ((((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law))).withDensity (fun u => ENNReal.ofReal
          (brownianVectorContinuousExponential W.B
            (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) T I u))).map Prod.fst =
              parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q) ∧
      ((((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law))).withDensity (fun u => ENNReal.ofReal
          (brownianVectorContinuousExponential W.B
            (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) T I u))).map
              (fun u => (u.1.1.2.1,u.1.2)) =
                (skDisorderLaw (ranks+q)).prod
                  (Measure.pi (fun _ : Fin (ranks+q) => scalarHiddenPriorBool 0))) := by
  obtain ⟨I,hI,hEi,hEprob,hEmarg⟩ := actualParisiGrowingReplayDReference_exists
    W β hβ δ hδ ranks q (brownianDyadicGrid T) 1 (brownianDyadicWidth T)
      (brownianDyadicWidth_tendsto T)
      (fun l d i _ => brownianDyadicGrid_left_le T l d i)
      (fun l i _ => brownianDyadicGrid_width_le T l i)
  simp only [brownianDyadicGrid_horizon] at hEi hEprob hEmarg
  exact ⟨I,hI,hEi,hEprob,hEmarg,
    parisiGrowingReplay_density_matrix_spin_marginal W δ (ranks+q) q _ hEmarg⟩

end SKConstants
