module

public import SKConstants.Completion.Y1.SourceIntegration
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine LQ N9 M1 Blueprint5
variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] fineCellRemovedSquare fineCellRemainingProjection
  M1.SourceTargets M1.Target M1.Update

theorem fineCellRemovedSquare_moments_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K) (e : Fin K) :
    (∫ z, fineCellRemovedSquare W β hβ δ r K e z ∂SourceLinkedLaw W β hβ δ r K) ≤
      (e.val : ℝ)*meshDuration δ e.val/(((r+K : ℕ) : ℝ)*(actualFineScale W β δ e.val)^2) ∧
    (∫ z, fineCellRemovedSquare W β hβ δ r K e z^2 ∂SourceLinkedLaw W β hβ δ r K) ≤
      3*(e.val : ℝ)^2*(meshDuration δ e.val)^2/
        (((r+K : ℕ) : ℝ)^2*(actualFineScale W β δ e.val)^4) := by
  let Q := freshRowsLaw W (growingQueryDuration δ e.val)
    (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K)
  letI : IsProbabilityMeasure Q := freshRowsLaw_probability W _ _ _
  letI : IsFiniteMeasure Q := IsZeroOrProbabilityMeasure.toIsFiniteMeasure Q
  letI : SigmaFinite Q := IsFiniteMeasure.toSigmaFinite Q
  letI : SFinite Q := inferInstance
  have hi := N9Y1.fineCellRemovedSquare_integrable W β hβ δ hδ r K hn e
  have hi2 := N9Y1.fineCellRemovedSquare_sq_integrable W β hβ δ hδ r K hn e
  have hi1 : Integrable (fun z => fineCellRemovedSquare W β hβ δ r K e z^1)
      (SourceLinkedLaw W β hβ δ r K) := by simpa only [pow_one] using hi
  have hF1 := fineCellRemovedSquare_integral_fresh W β hβ δ hδ r K e 1 hi1
  have hF2 := fineCellRemovedSquare_integral_fresh W β hβ δ hδ r K e 2 hi2
  simp only [pow_one] at hF1
  have hb := freshRemovedSquare_conditional_moments W β hβ δ hδ r K hn e
  rw [hF1.2,hF2.2]
  have h1 := integral_mono_ae hF1.1.integral_prod_left (integrable_const
    ((e.val : ℝ)*meshDuration δ e.val/(((r+K : ℕ) : ℝ)*(actualFineScale W β δ e.val)^2)))
    (hb.mono fun p hp => hp.1)
  have h2 := integral_mono_ae hF2.1.integral_prod_left (integrable_const
    (3*(e.val : ℝ)^2*(meshDuration δ e.val)^2/
      (((r+K : ℕ) : ℝ)^2*(actualFineScale W β δ e.val)^4)))
    (hb.mono fun p hp => hp.2)
  simpa only [integral_const,probReal_univ,one_smul] using And.intro h1 h2

theorem fineProjectionMomentStatement_holds : FineProjectionMomentStatement := by
  intro Ω _ W β hβ δ hδ r K hr _ e
  have hn : 0 < r+K := by omega
  have hm := fineCellRemovedSquare_moments_le W β hβ δ hδ r K hn e
  refine ⟨N9Y1.fineCellRemovedSquare_integrable W β hβ δ hδ r K hn e,
    N9Y1.fineCellRemovedSquare_sq_integrable W β hβ δ hδ r K hn e,hm.1.trans ?_,hm.2.trans ?_⟩
  · apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    apply mul_le_mul_of_nonneg_right _ (growingQueryDuration δ e.val).coe_nonneg
    exact_mod_cast Nat.le_succ e.val
  · apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) e.val]

end SKConstants.Completion.Y1
