module
public import SKConstants.Completion.LC4a.ReferenceMoments
public import Mathlib.InformationTheory.KullbackLeibler.Basic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem growingReplay_klDiv_eq_information
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q))
    [IsProbabilityMeasure (growingReplayDReference W β hβ δ hδ ranks q V I)] :
    klDiv (growingReplayLinkedLaw W β hβ δ ranks q V)
        (growingReplayDReference W β hβ δ hδ ranks q V I) =
      ENNReal.ofReal (∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
        ∂growingReplayLinkedLaw W β hβ δ ranks q V) := by
  let := growingReplayLinkedLaw_probability W β hβ δ hδ ranks q V
  let L := growingReplayLinkedLaw W β hβ δ ranks q V
  let R := growingReplayDReference W β hβ δ hδ ranks q V I
  have hac : L ≪ R := by
    change growingReplayLinkedLaw W β hβ δ ranks q V ≪ R
    rw [growingReplayLinkedLaw_eq_reference_withDensity W β hβ δ hδ ranks q V I hI]
    exact withDensity_absolutelyContinuous _ _
  have hRN := growingReplayLinkedLaw_rnDeriv_reference W β hβ δ hδ ranks q V I hI
  have hllr : llr L R =ᵐ[L] growingReplayInformation W β hβ δ hδ ranks q V I := by
    filter_upwards [hRN.filter_mono hac.ae_le] with u hu
    change Real.log ((L.rnDeriv R) u).toReal = _
    rw [hu, ENNReal.toReal_ofReal (div_pos
      (growingReplayLinkDensity_pos W β hβ δ ranks q V u)
      (growingReplayDExponential_pos W β hβ δ hδ ranks q V I u)).le]
    rfl
  have hint := (growingReplay_information_integrable W β hβ δ hδ ranks q V I hI).2.2
  rw [klDiv_of_ac_of_integrable hac (hint.congr hllr.symm), integral_congr_ae hllr]
  simp only [probReal_univ, add_sub_cancel_right]
  rfl

theorem actualReplay_finite_KL_exists
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    ∃ I : GrowingReplaySpace Ω δ ranks q → ℝ,
      IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I ∧
      IsProbabilityMeasure (growingReplayDReference W β hβ δ hδ ranks q V I) ∧
      Integrable I (growingReplayDReference W β hβ δ hδ ranks q V I) ∧
      Integrable (growingReplayInformation W β hβ δ hδ ranks q V I)
        (growingReplayLinkedLaw W β hβ δ ranks q V) ∧
      klDiv (growingReplayLinkedLaw W β hβ δ ranks q V)
          (growingReplayDReference W β hβ δ hδ ranks q V I) =
        ENNReal.ofReal (∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
          ∂growingReplayLinkedLaw W β hβ δ ranks q V) := by
  obtain ⟨I, hI, _, _, hprob, _, _⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ ranks q V
  let := hprob
  exact ⟨I, hI, hprob,
    growingReplayDIntegral_integrable_reference W β hβ δ hδ ranks q V I hI,
    (growingReplay_information_integrable W β hβ δ hδ ranks q V I hI.1).2.2,
    growingReplay_klDiv_eq_information W β hβ δ hδ ranks q V I hI.1⟩

theorem growingReplayDIntegral_klDiv_eq_information
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    klDiv (growingReplayLinkedLaw W β hβ δ ranks q V)
        (growingReplayDReference W β hβ δ hδ ranks q V I) =
      ENNReal.ofReal (∫ u, growingReplayInformation W β hβ δ hδ ranks q V I u
        ∂growingReplayLinkedLaw W β hβ δ ranks q V) := by
  let := growingReplayDIntegral_reference_probability W β hβ δ hδ ranks q V I hI
  exact growingReplay_klDiv_eq_information W β hβ δ hδ ranks q V I hI.1

end SKConstants.Completion.LC4a
