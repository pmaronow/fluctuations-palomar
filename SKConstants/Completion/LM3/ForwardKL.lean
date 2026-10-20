module
public import SKConstants.Completion.LM3.ReplayGibbsReference
public import SKConstants.Completion.LM3.DensityKL

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

def growingReplayGibbsLogRatio (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) (u : GrowingReplaySpace Ω δ ranks q) : ℝ :=
  growingReplayInformation W β hβ δ hδ ranks q V I u - (ranks + q : ℕ) * Real.log 2 +
    Real.log (gibbsPartition β (replayOutput δ ranks q u).1) -
      β * quadraticHamiltonian (replayOutput δ ranks q u).1 (replayOutput δ ranks q u).2

theorem growingReplayGibbsLogRatio_integrable
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q)) :
    Integrable (growingReplayGibbsLogRatio W β hβ δ hδ ranks q V I)
      (growingReplayLinkedLaw W β hβ δ ranks q V) := by
  let := growingReplayLinkedLaw_probability W β hβ δ hδ ranks q V
  have hp := gaussian_marginal_pressure_integrable
    (growingReplayLinkedLaw W β hβ δ ranks q V) β _ measurable_fst.fst.snd.fst
    (growingReplayLinkedLaw_matrix_marginal W β hβ δ hδ ranks q V)
  have he := (growingReplayLinkedLaw_energy_memLp W β hβ δ hδ ranks q V).integrable (by norm_num)
  exact ((((growingReplay_information_integrable W β hβ δ hδ ranks q V I hI).2.2).sub
    (integrable_const _)).add hp).sub (he.const_mul β)

theorem growingReplayGibbs_klDiv_eq
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    klDiv (growingReplayLinkedLaw W β hβ δ ranks q V)
      (growingReplayGibbsReference W β hβ δ hδ ranks q V I) =
      ENNReal.ofReal (∫ u, growingReplayGibbsLogRatio W β hβ δ hδ ranks q V I u
        ∂growingReplayLinkedLaw W β hβ δ ranks q V) := by
  let R := growingReplayDReference W β hβ δ hδ ranks q V I
  let f := fun u => growingReplayLinkDensity W β hβ δ ranks q V u /
    growingReplayDExponential W β hβ δ hδ ranks q V I u
  let g := fun u : GrowingReplaySpace Ω δ ranks q =>
    matrixGibbsDensity (ranks + q) β (replayOutput δ ranks q u)
  let := growingReplayDIntegral_reference_probability W β hβ δ hδ ranks q V I hI
  let := growingReplayLinkedLaw_probability W β hβ δ hδ ranks q V
  let := growingReplayGibbsReference_probability W β hβ δ hδ ranks q V I hI
  have hL : R.withDensity (fun u => ENNReal.ofReal (f u)) =
      growingReplayLinkedLaw W β hβ δ ranks q V :=
    (growingReplayLinkedLaw_eq_reference_withDensity W β hβ δ hδ ranks q V I hI.1).symm
  have hP : R.withDensity (fun u => ENNReal.ofReal (g u)) =
      growingReplayGibbsReference W β hβ δ hδ ranks q V I := rfl
  let _ : IsProbabilityMeasure (R.withDensity (fun u => ENNReal.ofReal (f u))) := by
    rw [hL]; infer_instance
  let _ : IsProbabilityMeasure (R.withDensity (fun u => ENNReal.ofReal (g u))) := by
    rw [hP]; infer_instance
  have hf : AEMeasurable f R :=
    ((measurable_growingReplayLinkDensity W β hβ δ hδ ranks q V).aemeasurable.div
      (aemeasurable_growingReplayDExponential W β hβ δ hδ ranks q V I hI.1)).mono_ac
        (withDensity_absolutelyContinuous _ _)
  have hg : Measurable g :=
    (measurable_matrixGibbsDensity (ranks + q) β).comp (measurable_replayOutput δ ranks q)
  have hpoint (u) : Real.log (f u) - Real.log (g u) =
      growingReplayGibbsLogRatio W β hβ δ hδ ranks q V I u := by
    dsimp only [f, g, growingReplayGibbsLogRatio, growingReplayInformation]
    rw [log_matrixGibbsDensity]
    ring
  have hint : Integrable (fun u => Real.log (f u) - Real.log (g u))
      (R.withDensity (fun u => ENNReal.ofReal (f u))) := by
    simp_rw [hpoint, hL]
    exact growingReplayGibbsLogRatio_integrable W β hβ δ hδ ranks q V I hI.1
  have h := klDiv_positive_densities_ae R f g hf hg.aemeasurable
    (fun u => div_pos (growingReplayLinkDensity_pos W β hβ δ ranks q V u)
      (growingReplayDExponential_pos W β hβ δ hδ ranks q V I u))
    (fun u => matrixGibbsDensity_pos (ranks + q) β _) hint
  simpa only [hL, hP, hpoint] using h

theorem growingReplayGibbsLogRatio_mean
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q)) :
    (∫ u, growingReplayGibbsLogRatio W β hβ δ hδ ranks q V I u
      ∂growingReplayLinkedLaw W β hβ δ ranks q V) =
      (∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
        ∂growingReplayLinkedLaw W β hβ δ ranks q V) - (ranks + q : ℕ) * Real.log 2 +
      (∫ G, Real.log (gibbsPartition β G) ∂skDisorderLaw (ranks + q)) -
      β * (∫ u, quadraticHamiltonian (replayOutput δ ranks q u).1
        (replayOutput δ ranks q u).2 ∂growingReplayLinkedLaw W β hβ δ ranks q V) := by
  let := growingReplayLinkedLaw_probability W β hβ δ hδ ranks q V
  have hi := (growingReplay_information_integrable W β hβ δ hδ ranks q V I hI).2.2
  have hc : Integrable (fun _ : GrowingReplaySpace Ω δ ranks q =>
      (ranks + q : ℕ) * Real.log 2) (growingReplayLinkedLaw W β hβ δ ranks q V) :=
    integrable_const _
  have hp := gaussian_marginal_pressure_integrable
    (growingReplayLinkedLaw W β hβ δ ranks q V) β _ measurable_fst.fst.snd.fst
    (growingReplayLinkedLaw_matrix_marginal W β hβ δ hδ ranks q V)
  have he := (growingReplayLinkedLaw_energy_memLp W β hβ δ hδ ranks q V).integrable (by norm_num)
  have hlaw : HasLaw (fun u => (replayOutput δ ranks q u).1) (skDisorderLaw (ranks + q))
      (growingReplayLinkedLaw W β hβ δ ranks q V) :=
    ⟨measurable_fst.fst.snd.fst.aemeasurable,
      growingReplayLinkedLaw_matrix_marginal W β hβ δ hδ ranks q V⟩
  have hpres := hlaw.integral_comp
    (Real.measurable_log.comp (continuous_gibbsPartition β).measurable).aestronglyMeasurable
  unfold growingReplayGibbsLogRatio
  dsimp only [replayOutput] at hp he hpres ⊢
  simp only [Function.comp_def] at hpres
  rw [integral_sub
      (f := fun u => growingReplayInformation W β hβ δ hδ ranks q V I u -
        (ranks + q : ℕ) * Real.log 2 + Real.log (gibbsPartition β u.1.1.2.1))
      (g := fun u => β * quadraticHamiltonian u.1.1.2.1 u.1.2) ((hi.sub hc).add hp) (he.const_mul β),
    integral_add
      (f := fun u => growingReplayInformation W β hβ δ hδ ranks q V I u -
        (ranks + q : ℕ) * Real.log 2) (g := fun u => Real.log (gibbsPartition β u.1.1.2.1))
      (hi.sub hc) hp, integral_sub hi hc,
    integral_const, probReal_univ, one_smul, integral_const_mul, hpres]

theorem actualReplay_forward_KL
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    klDiv ((growingReplayLinkedLaw W β hβ δ ranks q V).map (replayOutput δ ranks q))
      (skJointLaw (ranks + q) β) ≤
      ENNReal.ofReal ((∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
        ∂growingReplayLinkedLaw W β hβ δ ranks q V) - (ranks + q : ℕ) * Real.log 2 +
      (∫ G, Real.log (gibbsPartition β G) ∂skDisorderLaw (ranks + q)) -
      β * (∫ u, quadraticHamiltonian (replayOutput δ ranks q u).1
        (replayOutput δ ranks q u).2 ∂growingReplayLinkedLaw W β hβ δ ranks q V)) := by
  let := growingReplayLinkedLaw_probability W β hβ δ hδ ranks q V
  let := growingReplayGibbsReference_probability W β hβ δ hδ ranks q V I hI
  have h := klDiv_map_le (growingReplayLinkedLaw W β hβ δ ranks q V)
    (growingReplayGibbsReference W β hβ δ hδ ranks q V I) (measurable_replayOutput δ ranks q)
  rw [growingReplayGibbsReference_output_marginal W β hβ δ hδ ranks q V I hI,
    growingReplayGibbs_klDiv_eq W β hβ δ hδ ranks q V I hI,
    growingReplayGibbsLogRatio_mean W β hβ δ hδ ranks q V I hI.1] at h
  exact h

end SKConstants.Completion.LM3
