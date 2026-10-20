module

public import SKConstants.Completion.N13t.Integrals

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N13t
open SKConstantsOAI.ZeroTemperatureSK LC4a

variable {Ω : Type*} [MeasurableSpace Ω]

theorem growingReplayDIntegral_measurable_version
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ r q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r q V I) :
    ∃ J, Measurable J ∧ IsGrowingReplayDIntegral W β hβ δ hδ r q V J ∧
      I =ᵐ[growingReplayUnlinkedLaw W δ r q] J := by
  let J := hI.1.aestronglyMeasurable.mk I
  have he : I =ᵐ[growingReplayUnlinkedLaw W δ r q] J := hI.1.aestronglyMeasurable.ae_eq_mk
  have herr (l : ℕ) : (fun u => (growingReplayDLeftSum W β hβ δ hδ r q V l u - I u) ^ 2) =ᵐ[
      growingReplayUnlinkedLaw W δ r q]
      fun u => (growingReplayDLeftSum W β hβ δ hδ r q V l u - J u) ^ 2 :=
    he.mono (fun u hu => by dsimp only; rw [hu])
  exact ⟨J, hI.1.aestronglyMeasurable.measurable_mk,
    ⟨hI.1.ae_eq he, fun l => (hI.2.1 l).congr (herr l),
      hI.2.2.congr' (Eventually.of_forall fun l => integral_congr_ae (herr l))⟩, he⟩

theorem growingReplayLinkedLaw_inverse_information
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ r q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r q V I) :
    (growingReplayLinkedLaw W β hβ δ r q V).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-growingReplayInformation W β hβ δ hδ r q V I u))) =
      growingReplayDReference W β hβ δ hδ r q V I := by
  have hlink : AEMeasurable (growingReplayLinkDensity W β hβ δ r q V)
      (growingReplayUnlinkedLaw W δ r q) :=
    (measurable_growingReplayLinkDensity W β hβ δ hδ r q V).aemeasurable
  have hexp := aemeasurable_growingReplayDExponential W β hβ δ hδ r q V I hI.1
  have hpos := growingReplayLinkDensity_pos W β hβ δ r q V
  have he : (fun u => Real.exp (-growingReplayInformation W β hβ δ hδ r q V I u)) =
      fun u => growingReplayDExponential W β hβ δ hδ r q V I u /
        growingReplayLinkDensity W β hβ δ r q V u := by
    funext u
    rw [growingReplayInformation, Real.exp_neg,
      Real.exp_log (div_pos (hpos u) (growingReplayDExponential_pos W β hβ δ hδ r q V I u))]
    exact inv_div _ _
  simp_rw [show ∀ u, Real.exp (-growingReplayInformation W β hβ δ hδ r q V I u) =
    growingReplayDExponential W β hβ δ hδ r q V I u /
      growingReplayLinkDensity W β hβ δ r q V u from congrFun he]
  exact (positive_density_ratio_withDensity (growingReplayUnlinkedLaw W δ r q)
    (growingReplayDExponential W β hβ δ hδ r q V I)
    (growingReplayLinkDensity W β hβ δ r q V) hexp hlink hpos).symm

theorem growingReplay_inverse_information_matrix_spin_marginal
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ r q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ r q V I) :
    ((growingReplayLinkedLaw W β hβ δ r q V).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-growingReplayInformation W β hβ δ hδ r q V I u)))).map
        (fun u => (u.1.1.2.1, u.1.2)) =
      (skDisorderLaw (r + q)).prod
        (Measure.pi fun _ : Fin (r + q) => scalarHiddenPriorBool 0) := by
  rw [growingReplayLinkedLaw_inverse_information W β hβ δ hδ r q V I hI]
  obtain ⟨J, hJ, _, _, _, _, hMarg⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ r q V
  rw [growingReplayDReference_unique W β hβ δ hδ r q V I J hI hJ]
  exact hMarg

end SKConstants.Completion.N13t
