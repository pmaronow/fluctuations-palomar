module

public import SKConstants.Completion.LBase.TerminalProfile
public import SKConstants.Completion.LBase.UniformLower

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_row_proxy_temperature_shift_log_bound
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (A L : ℝ) (n : ℕ) (H : ℝ≥0) (hn : 0 < n)
    (hH : (H : ℝ) ≤ A + L * Real.log (n : ℝ)) :
    (actualParisiPosteriorRowMGFProxy W β H : ℝ) ≤
      (1 / curvatureLowerConstant β) * Real.exp (A / 2) * (n : ℝ)^(L / 2) *
        Real.sqrt (1 + A + L * Real.log (n : ℝ)) := by
  have hc := curvatureLowerConstant_pos β hβ
  calc
    _ ≤ (1 / curvatureLowerConstant β) * Real.exp ((H : ℝ) / 2) * Real.sqrt (1 + (H : ℝ)) :=
      actual_row_proxy_temperature_bound W β hβ H
    _ ≤ (1 / curvatureLowerConstant β) * Real.exp ((A + L * Real.log (n : ℝ)) / 2) *
        Real.sqrt (1 + A + L * Real.log (n : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
      · exact Real.sqrt_le_sqrt (by linarith)
      · positivity
      · positivity
    _ = _ := by rw [exp_half_shift_log A L n hn]; ring

theorem actual_inverse_temperature_shift_log_bound
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (A L : ℝ) (n : ℕ) (s H : ℝ≥0) (hn : 0 < n) (hsH : s ≤ H)
    (hH : (H : ℝ) ≤ A + L * Real.log (n : ℝ)) :
    1 / actualParisiFullSusceptibilitySquareExpected W β s ≤
      (1 / curvatureLowerConstant β) * Real.exp (A / 2) * (n : ℝ)^(L / 2) *
        Real.sqrt (1 + A + L * Real.log (n : ℝ)) :=
  (actual_inverse_profile_le_terminal W β hβ s H hsH).trans
    (actual_row_proxy_temperature_shift_log_bound W β hβ A L n H hn hH)

theorem actual_scalar_tails (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    0 < terminalTailConstant β ∧ 0 < curvatureLowerConstant β ∧
    (∀ t : ℝ, 0 ≤ t →
      actualParisiFullSusceptibilityExpected W β t ≤
        terminalTailConstant β * (Real.exp (-t / 2) / Real.sqrt (1 + t)) ∧
      curvatureLowerConstant β * (Real.exp (-t / 2) / Real.sqrt (1 + t)) ≤
        actualParisiFullSusceptibilitySquareExpected W β t) ∧
    (∀ s H : ℝ≥0, s ≤ H →
      1 / actualParisiFullSusceptibilitySquareExpected W β s ≤
        (1 / curvatureLowerConstant β) * Real.exp ((H : ℝ) / 2) * Real.sqrt (1 + (H : ℝ))) := by
  refine ⟨terminalTailConstant_pos β, curvatureLowerConstant_pos β hβ, ?_, ?_⟩
  · intro t ht
    exact ⟨actual_susceptibility_global_tail W β hβ t ht,
      actual_square_profile_temperature_lower W β hβ t ht⟩
  · intro s H hsH
    exact (actual_inverse_profile_le_terminal W β hβ s H hsH).trans
      (actual_row_proxy_temperature_bound W β hβ H)

end SKConstants.Completion.LBase
