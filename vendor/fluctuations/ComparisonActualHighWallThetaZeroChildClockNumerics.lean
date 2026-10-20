module

public import ComparisonActualHighWallThetaZeroSelectedScale
public import ComparisonActualHighWallChildClockIncrements

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

theorem eventually_theta_zero_child_numeric_clock_increments_from_target
    {m delta cl cu Az C0 Ct D Bclock c0:ℝ}
    (hdelta:0<delta) (hC0:0<C0) (hc0:0<c0) (hc01:c0≤1)
    {eta C:ℝ} (heta:0<eta) (heta1:eta≤1) (hC:1≤C)
    (hmargin:0<9*m-298*delta):
    ∀ᶠn:ℕ in atTop,∀M:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs≤1 → comparisonConditionalScale M.data.N delta M.data.E M.lam≤M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs≤(eta*c0)^3*M.xs^2 →
      ∀r∈Icc (0:ℝ) 1,r≤C*M.xs →
        laplaceComparisonStrength M.data.d M.lam r≤
          eta^2*(actualChildCutoff (n+1) delta c0 M.data.d M.lam M.xs)^2 ∧
        laplaceComparisonStrength M.data.d M.lam r*r≤
          C*eta^3*(actualChildCutoff (n+1) delta c0 M.data.d M.lam M.xs)^3:=by
  have hnEvent:=eventually_actual_child_numeric_clock_increments_from_target
    (m:=m) (delta:=delta) (C0:=C0) (c0:=c0)
    hdelta hC0 hc0 hc01 heta heta1 hC hmargin
  have hdim:Tendsto (fun n:ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [hdim.eventually hnEvent] with n hn
  intro M hunit htarget hweak r hr hrC
  have hlo:(1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d≤M.data.E:=by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup:M.data.E≤M.data.d^2/Real.sqrt M.data.N:=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr
      (by simpa only [mul_comm] using M.hupper)
  exact hn M.data.d M.lam M.data.E M.xs M.data.hd M.hlam M.hld M.data.hE
    hlo hup ⟨M.hxs,hunit⟩ htarget hweak r hr hrC

theorem eventually_theta_zero_strength_le_child_cutoff_sq
    {m delta cl cu Az C0 Ct D Bclock c0:ℝ}
    (hdelta:0<delta) (hC0:0<C0) (hc0:0<c0) (hc01:c0≤1)
    {eta:ℝ} (heta:0<eta) (heta1:eta≤1)
    (hmargin:0<9*m-298*delta):
    ∀ᶠn:ℕ in atTop,∀M:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs≤1 → comparisonConditionalScale M.data.N delta M.data.E M.lam≤M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs≤(eta*c0)^3*M.xs^2 →
      M.lam≤eta^2*(actualChildCutoff (n+1) delta c0 M.data.d M.lam M.xs)^2:=by
  filter_upwards [eventually_theta_zero_child_numeric_clock_increments_from_target
    (m:=m) (delta:=delta) (C0:=C0) (c0:=c0)
    hdelta hC0 hc0 hc01 heta heta1 (show (1:ℝ)≤1 by norm_num) hmargin]
    with n hn
  intro M hunit htarget hweak
  have H:= (hn M hunit htarget hweak 0 ⟨le_rfl,zero_le_one⟩
    (mul_nonneg zero_le_one M.hxs.le)).1
  simpa only [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape,
    mul_zero,zero_div,ite_eq_left (by norm_num:(0:ℝ)≤1),mul_one] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
