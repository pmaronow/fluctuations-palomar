module

public import ComparisonActualHighOnlyConditionalDensityBasics

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

theorem comparison_conditional_full_error_absorption_high_only
    {C delta:ℝ} (hC:0 ≤ C) (hdelta:0 < delta) :
    ∀ᶠN:ℝ in atTop,∀E:ℝ,0 ≤ E →
      C*(1+Real.log N)*N^(7*delta)*E+C*N^(3*delta)*E+C*N^(2*delta)*E ≤ N^(10*delta)*E := by
  have HL:=comparison_log_loss_eventually (C:=4*C) (p:=1) (by positivity) hdelta
  filter_upwards [HL,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with N hnLoss hN hlog
  intro E hE
  have hNpos:0 < N:=zero_lt_one.trans_le hN
  have H3:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (show 3*delta ≤ 7*delta by linarith)) hE
  have H2:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (show 2*delta ≤ 7*delta by linarith)) hE
  have HC3:=mul_le_mul_of_nonneg_left H3 hC
  have HC2:=mul_le_mul_of_nonneg_left H2 hC
  have Hcoef:C*(3+Real.log N) ≤ 4*C*Real.log N:=by
    have H:=mul_le_mul_of_nonneg_left hlog hC
    nlinarith only [H]
  simp only [Real.rpow_one] at hnLoss
  have Hmain:=mul_le_mul_of_nonneg_right (Hcoef.trans hnLoss)
    (show 0 ≤ N^(7*delta)*E by positivity)
  have HE:N^delta*(N^(7*delta)*E)=N^(8*delta)*E:=by
    rw [←mul_assoc,←Real.rpow_add hNpos];congr 2;ring
  rw [HE] at Hmain
  have Hlast:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (show 8*delta ≤ 10*delta by linarith)) hE
  have Hfull:C*(1+Real.log N)*N^(7*delta)*E+C*N^(3*delta)*E+C*N^(2*delta)*E ≤
      C*(3+Real.log N)*(N^(7*delta)*E):=by
    nlinarith only [HC3,HC2]
  exact Hfull.trans (Hmain.trans Hlast)

end OAI.SKFluctuations.LaplaceWindowFormalization
