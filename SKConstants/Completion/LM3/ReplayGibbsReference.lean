module
public import SKConstants.Completion.LM3.GibbsTilt

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a GaussianProposal
variable {Ω : Type*} [MeasurableSpace Ω]

def replayOutput (δ : ℝ≥0) (ranks q : ℕ) (u : GrowingReplaySpace Ω δ ranks q) :
    Matrix (Fin (ranks + q)) (Fin (ranks + q)) ℝ × Spin (ranks + q) :=
  (u.1.1.2.1, u.1.2)

theorem measurable_replayOutput (δ : ℝ≥0) (ranks q : ℕ) :
    Measurable (replayOutput (Ω := Ω) δ ranks q) :=
  measurable_fst.fst.snd.fst.prodMk measurable_fst.snd

theorem growingReplayLinkedLaw_matrix_marginal
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    (growingReplayLinkedLaw W β hβ δ ranks q V).map
      (fun u => (replayOutput δ ranks q u).1) = skDisorderLaw (ranks + q) := by
  let := W.isProbability
  let θ : GrowingReplaySpace Ω δ ranks q →
      ScalarGrowingReplayStaticData δ (ranks + q) q × (Fin (ranks + q) → Ω) :=
    fun u => (u.1.1, u.2)
  have hθ : Measurable θ := measurable_fst.fst.prodMk measurable_snd
  have hstatic : MeasurePreserving (fun a : ScalarGrowingReplayStaticData δ (ranks + q) q => a.2.1)
      (scalarGrowingReplayStaticLaw W δ (ranks + q) q) (skDisorderLaw (ranks + q)) :=
    (measurePreserving_fst (μ := skDisorderLaw (ranks + q))
      (ν := paperCompletionNoiseLaw (ranks + q) q)).comp
      (measurePreserving_snd (μ := _) (ν := (skDisorderLaw (ranks + q)).prod
        (paperCompletionNoiseLaw (ranks + q) q)))
  have hm := hstatic.comp (measurePreserving_fst
    (μ := scalarGrowingReplayStaticLaw W δ (ranks + q) q)
    (ν := Measure.pi (fun _ : Fin (ranks + q) => W.law)))
  change (growingReplayLinkedLaw W β hβ δ ranks q V).map
    (((fun a : ScalarGrowingReplayStaticData δ (ranks + q) q => a.2.1) ∘
      (Prod.fst : ScalarGrowingReplayStaticData δ (ranks + q) q ×
        (Fin (ranks + q) → Ω) → _)) ∘ θ) = _
  rw [← Measure.map_map hm.measurable hθ,
    growingReplayLinkedLaw_path_marginal W β hβ δ hδ ranks q V]
  exact hm.map_eq

theorem growingReplayDIntegral_output_marginal
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    (growingReplayDReference W β hβ δ hδ ranks q V I).map (replayOutput δ ranks q) =
      (skDisorderLaw (ranks + q)).prod (M1.spinPrior (ranks + q)) := by
  obtain ⟨J, hJ, _, _, _, _, hmarg⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ ranks q V
  rw [growingReplayDReference_unique W β hβ δ hδ ranks q V I J hI hJ]
  exact hmarg

def growingReplayGibbsReference
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) : Measure (GrowingReplaySpace Ω δ ranks q) :=
  (growingReplayDReference W β hβ δ hδ ranks q V I).withDensity
    (fun u => ENNReal.ofReal (matrixGibbsDensity (ranks + q) β (replayOutput δ ranks q u)))

theorem growingReplayGibbsReference_output_marginal
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    (growingReplayGibbsReference W β hβ δ hδ ranks q V I).map (replayOutput δ ranks q) =
      skJointLaw (ranks + q) β := by
  unfold growingReplayGibbsReference
  rw [show (fun u : GrowingReplaySpace Ω δ ranks q => ENNReal.ofReal
      (matrixGibbsDensity (ranks + q) β (replayOutput δ ranks q u))) =
    (fun p => ENNReal.ofReal (matrixGibbsDensity (ranks + q) β p)) ∘
      replayOutput δ ranks q by rfl,
    map_withDensity_comp _ _ (measurable_replayOutput δ ranks q) _
      (measurable_matrixGibbsDensity (ranks + q) β).ennreal_ofReal,
    growingReplayDIntegral_output_marginal W β hβ δ hδ ranks q V I hI,
    matrixGibbsDensity_withDensity]

theorem growingReplayGibbsReference_probability
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    IsProbabilityMeasure (growingReplayGibbsReference W β hβ δ hδ ranks q V I) := by
  constructor
  have h : ((growingReplayGibbsReference W β hβ δ hδ ranks q V I).map
      (replayOutput δ ranks q)) univ = 1 := by
    rw [growingReplayGibbsReference_output_marginal W β hβ δ hδ ranks q V I hI,
      measure_univ]
  rw [Measure.map_apply (measurable_replayOutput δ ranks q) MeasurableSet.univ,
    preimage_univ] at h
  exact h

theorem growingReplayLinkedLaw_energy_memLp
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    MemLp (fun u => quadraticHamiltonian (replayOutput δ ranks q u).1
      (replayOutput δ ranks q u).2) 2 (growingReplayLinkedLaw W β hβ δ ranks q V) :=
  LF0.gaussian_marginal_energy_memLp _ _ _
    measurable_fst.fst.snd.fst measurable_fst.snd
    (growingReplayLinkedLaw_matrix_marginal W β hβ δ hδ ranks q V)

theorem growingReplayLinkedLaw_energy_second_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (hn : 0 < ranks + q) :
    (∫ u, (quadraticHamiltonian (replayOutput δ ranks q u).1
      (replayOutput δ ranks q u).2)^2 ∂growingReplayLinkedLaw W β hβ δ ranks q V) ≤
      ((ranks + q : ℕ) : ℝ)^2 * (((ranks + q : ℕ) : ℝ) + 1) / 4 :=
  LF0.gaussian_marginal_energy_second_moment _ hn _ _
    measurable_fst.fst.snd.fst measurable_fst.snd
    (growingReplayLinkedLaw_matrix_marginal W β hβ δ hδ ranks q V)

end SKConstants.Completion.LM3
