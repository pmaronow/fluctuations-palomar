module
public import SKConstants.Completion.LC4a.ReplayDIntegral
public import SKConstants.Completion.LC4a.PositiveDensity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def growingReplayInformation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) (u : GrowingReplaySpace Ω δ ranks q) : ℝ :=
  Real.log (growingReplayLinkDensity W β hβ δ ranks q V u /
    growingReplayDExponential W β hβ δ hδ ranks q V I u)

lemma growingReplayDExponential_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) (u : GrowingReplaySpace Ω δ ranks q) :
    0 < growingReplayDExponential W β hβ δ hδ ranks q V I u := Real.exp_pos _

lemma integrable_growingReplayDBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    Integrable (growingReplayDBracket W β hβ δ hδ ranks q V)
      (growingReplayUnlinkedLaw W δ ranks q) := by
  apply Integrable.of_bound (aestronglyMeasurable_growingReplayDBracket W β hβ δ hδ ranks q V)
    (4 * (ranks + q : ℕ) * (V : ℝ))
  exact ae_of_all _ (fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (growingReplayDBracket_bounds W β hβ δ hδ ranks q V u).1]
    exact (growingReplayDBracket_bounds W β hβ δ hδ ranks q V u).2)

lemma aemeasurable_growingReplayDExponential (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q)) :
    AEMeasurable (growingReplayDExponential W β hβ δ hδ ranks q V I)
      (growingReplayUnlinkedLaw W δ ranks q) :=
  (hI.aemeasurable.sub
    ((aestronglyMeasurable_growingReplayDBracket W β hβ δ hδ ranks q V).aemeasurable.div_const 2)).exp

theorem growingReplayLinkedLaw_eq_reference_withDensity
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q)) :
    growingReplayLinkedLaw W β hβ δ ranks q V =
      (growingReplayDReference W β hβ δ hδ ranks q V I).withDensity (fun u =>
        ENNReal.ofReal (growingReplayLinkDensity W β hβ δ ranks q V u /
          growingReplayDExponential W β hβ δ hδ ranks q V I u)) :=
  positive_density_ratio_withDensity _ _ _
    (measurable_growingReplayLinkDensity W β hβ δ hδ ranks q V).aemeasurable
    (aemeasurable_growingReplayDExponential W β hβ δ hδ ranks q V I hI)
    (growingReplayDExponential_pos W β hβ δ hδ ranks q V I)

theorem growingReplayLinkedLaw_rnDeriv_reference
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q))
    [IsFiniteMeasure (growingReplayDReference W β hβ δ hδ ranks q V I)] :
    (growingReplayLinkedLaw W β hβ δ ranks q V).rnDeriv
        (growingReplayDReference W β hβ δ hδ ranks q V I) =ᵐ[
          growingReplayDReference W β hβ δ hδ ranks q V I]
      fun u => ENNReal.ofReal (growingReplayLinkDensity W β hβ δ ranks q V u /
        growingReplayDExponential W β hβ δ hδ ranks q V I u) := by
  have hm := ((measurable_growingReplayLinkDensity W β hβ δ hδ ranks q V).aemeasurable.div
    (aemeasurable_growingReplayDExponential W β hβ δ hδ ranks q V I hI)).ennreal_ofReal
  have hmR : AEMeasurable (fun u => ENNReal.ofReal
      (growingReplayLinkDensity W β hβ δ ranks q V u /
        growingReplayDExponential W β hβ δ hδ ranks q V I u))
      (growingReplayDReference W β hβ δ hδ ranks q V I) :=
    hm.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [growingReplayLinkedLaw_eq_reference_withDensity W β hβ δ hδ ranks q V I hI]
  exact Measure.rnDeriv_withDensity₀ _ hmR

lemma growingReplayInformation_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) (u : GrowingReplaySpace Ω δ ranks q) :
    growingReplayInformation W β hβ δ hδ ranks q V I u =
      Real.log (growingReplayLinkDensity W β hβ δ ranks q V u) - I u +
        growingReplayDBracket W β hβ δ hδ ranks q V u / 2 := by
  rw [growingReplayInformation, Real.log_div
    (growingReplayLinkDensity_pos W β hβ δ ranks q V u).ne'
    (growingReplayDExponential_pos W β hβ δ hδ ranks q V I u).ne']
  simp only [growingReplayDExponential, brownianVectorContinuousExponential, Real.log_exp,
    growingReplayDBracket]
  ring

lemma integrable_under_growingReplayLink (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    {F : GrowingReplaySpace Ω δ ranks q → ℝ}
    (hF : Integrable F (growingReplayUnlinkedLaw W δ ranks q)) :
    Integrable F (growingReplayLinkedLaw W β hβ δ ranks q V) :=
  integrable_withDensity_of_bounded _ _
    (measurable_growingReplayLinkDensity W β hβ δ hδ ranks q V)
    (fun u => (growingReplayLinkDensity_pos W β hβ δ ranks q V u).le) _
    (growingReplayLinkDensity_le W β hβ δ ranks q V) hF

lemma integrable_log_growingReplayLink (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    Integrable (fun u => Real.log (growingReplayLinkDensity W β hβ δ ranks q V u))
      (growingReplayLinkedLaw W β hβ δ ranks q V) :=
  integrable_log_withDensity_of_bounded _ _
    (measurable_growingReplayLinkDensity W β hβ δ hδ ranks q V)
    (fun u => (growingReplayLinkDensity_pos W β hβ δ ranks q V u).le) _
    (growingReplayLinkDensity_le W β hβ δ ranks q V)

theorem growingReplay_information_integrable
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q)) :
    Integrable I (growingReplayUnlinkedLaw W δ ranks q) ∧
      Integrable I (growingReplayLinkedLaw W β hβ δ ranks q V) ∧
      Integrable (growingReplayInformation W β hβ δ hδ ranks q V I)
        (growingReplayLinkedLaw W β hβ δ ranks q V) := by
  have hi : Integrable I (growingReplayUnlinkedLaw W δ ranks q) := hI.integrable (by norm_num)
  have hiL := integrable_under_growingReplayLink W β hβ δ hδ ranks q V hi
  have hqL := integrable_under_growingReplayLink W β hβ δ hδ ranks q V
    (integrable_growingReplayDBracket W β hβ δ hδ ranks q V)
  refine ⟨hi, hiL, ?_⟩
  convert ((integrable_log_growingReplayLink W β hβ δ hδ ranks q V).sub hiL).add
    (hqL.div_const 2) using 1
  funext u
  exact growingReplayInformation_eq W β hβ δ hδ ranks q V I u

theorem growingReplay_information_mean_decomposition
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q)) :
    (∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
      ∂growingReplayLinkedLaw W β hβ δ ranks q V) =
      (∫ u, Real.log (growingReplayLinkDensity W β hβ δ ranks q V u)
        ∂growingReplayLinkedLaw W β hβ δ ranks q V) -
      (∫ u, I u ∂growingReplayLinkedLaw W β hβ δ ranks q V) +
      (∫ u, growingReplayDBracket W β hβ δ hδ ranks q V u
        ∂growingReplayLinkedLaw W β hβ δ ranks q V) / 2 := by
  have hi := (growingReplay_information_integrable W β hβ δ hδ ranks q V I hI).2.1
  have hl := integrable_log_growingReplayLink W β hβ δ hδ ranks q V
  have hq := integrable_under_growingReplayLink W β hβ δ hδ ranks q V
    (integrable_growingReplayDBracket W β hβ δ hδ ranks q V)
  simp_rw [growingReplayInformation_eq]
  rw [integral_add (f := fun u => Real.log (growingReplayLinkDensity W β hβ δ ranks q V u) - I u)
    (g := fun u => growingReplayDBracket W β hβ δ hδ ranks q V u / 2) (hl.sub hi) (hq.div_const 2),
    integral_sub (f := fun u => Real.log (growingReplayLinkDensity W β hβ δ ranks q V u))
      (g := I) hl hi, integral_div]

theorem actualReplay_linked_reference_exists
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    ∃ I : GrowingReplaySpace Ω δ ranks q → ℝ,
      IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I ∧
      IsProbabilityMeasure (growingReplayDReference W β hβ δ hδ ranks q V I) ∧
      (growingReplayDReference W β hβ δ hδ ranks q V I).map Prod.fst =
        parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q ∧
      (growingReplayDReference W β hβ δ hδ ranks q V I).map (fun u => (u.1.1.2.1, u.1.2)) =
        (skDisorderLaw (ranks + q)).prod
          (Measure.pi (fun _ : Fin (ranks + q) => scalarHiddenPriorBool 0)) ∧
      growingReplayLinkedLaw W β hβ δ ranks q V =
        (growingReplayDReference W β hβ δ hδ ranks q V I).withDensity (fun u =>
          ENNReal.ofReal (growingReplayLinkDensity W β hβ δ ranks q V u /
            growingReplayDExponential W β hβ δ hδ ranks q V I u)) ∧
      Integrable I (growingReplayLinkedLaw W β hβ δ ranks q V) ∧
      Integrable (growingReplayInformation W β hβ δ hδ ranks q V I)
        (growingReplayLinkedLaw W β hβ δ ranks q V) := by
  obtain ⟨I, hI, _, _, hprob, hmarg, hmat⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ ranks q V
  have hint := growingReplay_information_integrable W β hβ δ hδ ranks q V I hI.1
  exact ⟨I, hI, hprob, hmarg, hmat,
    growingReplayLinkedLaw_eq_reference_withDensity W β hβ δ hδ ranks q V I hI.1,
    hint.2.1, hint.2.2⟩

end SKConstants.Completion.LC4a
