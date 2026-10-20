module
public import SKConstants.ParisiVectorDReference
public import SKConstants.GaussianProposalActualParisiCallbacks
public import SKConstants.ScalarProcessParisiRho

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK

abbrev ParisiGrowingReplaySpinStatic (δ : ℝ≥0) (n q : ℕ) :=
  ScalarGrowingReplayStaticData δ n q × (Fin n → Bool)

def parisiGrowingReplaySpinStaticLaw {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    Measure (ParisiGrowingReplaySpinStatic δ n q) :=
  (scalarGrowingReplayStaticLaw W δ n q).prod (Measure.pi (fun _ : Fin n => scalarHiddenPriorBool 0))

instance parisiGrowingReplaySpinStaticLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (δ : ℝ≥0) (n q : ℕ) :
    IsProbabilityMeasure (parisiGrowingReplaySpinStaticLaw W δ n q) := by
  unfold parisiGrowingReplaySpinStaticLaw
  infer_instance

def actualParisiGrowingSpinReplayFieldPast {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :
    BrownianVectorPastField (ParisiGrowingReplaySpinStatic δ (ranks+q) q) (Fin (ranks+q)) :=
  fun t u => actualParisiGrowingReplayPastCallback W β hβ δ hδ ranks q t (u.1.1,u.2)

lemma measurable_actualParisiGrowingSpinReplayFieldPast {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (t : ℝ≥0) :
    Measurable (actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q t) :=
  (measurable_actualParisiGrowingReplayPastCallback W β hβ δ hδ ranks q t).comp
    (measurable_fst.fst.prodMk measurable_snd)

lemma actualParisiGrowingSpinReplayFieldPast_continuous_ae {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (i : Fin (ranks+q)) :
    ∀ᵐ u ∂(parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law)),
      Continuous (fun t => actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q t
        (u.1,brownianVectorFullPast W.B t u.2) i) := by
  let := W.isProbability
  let P := scalarGrowingReplayStaticLaw W δ (ranks+q) q
  let S := Measure.pi (fun _ : Fin (ranks+q) => scalarHiddenPriorBool 0)
  let D := Measure.pi (fun _ : Fin (ranks+q) => W.law)
  have hMP : MeasurePreserving (fun u : ParisiGrowingReplaySpinStatic δ (ranks+q) q ×
      (Fin (ranks+q) → Ω) => (u.1.1,u.2)) ((P.prod S).prod D) (P.prod D) :=
    (measurePreserving_fst (μ := P) (ν := S)).prod (MeasurePreserving.id D)
  have hc := hMP.quasiMeasurePreserving.ae
    (actualParisiGrowingReplayPastCallback_continuous_brownian_ae W β hβ δ hδ ranks q P)
  filter_upwards [hc] with u hu
  exact continuous_pi_iff.mp hu i

def actualParisiGrowingReplayDCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :=
  actualParisiVectorDCoefficient β (Prod.snd : ParisiGrowingReplaySpinStatic δ (ranks+q) q → _)
    (fun t : ℝ≥0 => actualParisiQuerySigma W β t)
    (actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q)

theorem actualParisiGrowingReplayDReference_exists {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ)
    (G : ScalarDyadicNestedGrid) (k : ℕ) (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ η l)
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ η l) :
    ∃ I : ParisiGrowingReplaySpinStatic δ (ranks+q) q × (Fin (ranks+q) → Ω) → ℝ,
      MemLp I 2 ((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law))) ∧
      Integrable (brownianVectorContinuousExponential W.B
        (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) (G.time 0 k) I)
          ((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
            (Measure.pi (fun _ : Fin (ranks+q) => W.law))) ∧
      IsProbabilityMeasure (((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law))).withDensity (fun u => ENNReal.ofReal
          (brownianVectorContinuousExponential W.B (actualParisiGrowingReplayDCoefficient
            W β hβ δ hδ ranks q) (G.time 0 k) I u))) ∧
      ((((parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) => W.law))).withDensity (fun u => ENNReal.ofReal
          (brownianVectorContinuousExponential W.B (actualParisiGrowingReplayDCoefficient
            W β hβ δ hδ ranks q) (G.time 0 k) I u))).map Prod.fst =
              parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q) := by
  let := W.isProbability
  obtain ⟨I,hI,hIlim,hEi,hEmean,hEprob,hEmarg⟩ := actualParisiVectorDReference_exists
    (parisiGrowingReplaySpinStaticLaw W δ (ranks+q) q) W.law W.B W.brownian.toIsPreBrownianReal W.measurable
    β Prod.snd measurable_snd (fun t : ℝ≥0 => actualParisiQuerySigma W β t)
    ((continuous_actualParisiQuerySigma W β).comp NNReal.continuous_coe)
    (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (actualParisiQuerySigma_bounds W β hβ t).1]
                 exact (actualParisiQuerySigma_bounds W β hβ t).2)
    (actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q)
    (measurable_actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q)
    (actualParisiGrowingSpinReplayFieldPast_continuous_ae W β hβ δ hδ ranks q)
    G k η hη hleft hwidth
  exact ⟨I,hI,hEi,hEprob,hEmarg⟩

end SKConstants
