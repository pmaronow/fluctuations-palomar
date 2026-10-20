module

public import SKConstants.Completion.N13bc.WeightedRate

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace
namespace SKConstants.Completion.N13bc
open SKConstantsOAI.ZeroTemperatureSK LW

def GrowingPaddedWeightedStatement : Prop :=
  ∀ {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0), 0 < δ → ∀ (k r : ℕ) (h : k ≤ 2^r),
    (∀ j < k, LQ.meshDuration δ j ≤ 1) → ∀ (n : ℕ), 0 < n →
    ∀ η : ℝ, 0 < η →
    let t := growingQueryTime δ
    let V := t (k+1)
    let R : ℝ := actualParisiPosteriorRowMGFProxy W β V
    (linkedScalarRowsLaw W Z β V n).real
      {ω | 4*η^2*(2+5*(r+1 : ℝ)*(t k : ℝ)) <
        actualPaddedWeightedSq W Z β hβ t V k r h ω} ≤
      sevenTailBudget n r (Real.exp (1/8)) R η

theorem growingPaddedWeightedStatement_holds : GrowingPaddedWeightedStatement := by
  intro Ω A _ _ W Z β hβ δ hδ k r h hsmall n hn η hη
  dsimp only
  have hR : (1 : ℝ) ≤ actualParisiPosteriorRowMGFProxy W β (growingQueryTime δ (k+1)) :=
    NNReal.coe_le_coe.mpr (actualParisiPosteriorRowMGFProxy_one_le W β hβ _)
  have H := actual_padded_weightedSq_tail_explicit W Z β hβ (growingQueryTime δ)
    (growingQueryTime_strictMono δ hδ) (growingQueryTime δ (k+1)) k r h le_rfl
    (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1/8)) hR le_rfl
    (growing_real_weight_bound W β hβ δ hδ k hsmall) hn hη
  simpa only [growingQueryTime_zero, NNReal.coe_zero, sub_zero, sevenTailBudget] using H

end SKConstants.Completion.N13bc
