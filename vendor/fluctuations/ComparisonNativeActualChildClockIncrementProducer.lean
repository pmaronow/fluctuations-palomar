module

public import ComparisonNativeActualHistoryCutoffLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem eventually_actual_child_clock_increments_from_target
    (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    {eta C : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) (hC : 1 ≤ C)
    (hmargin : 0 < 9*m-298*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(P : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      x∈Ioc (0:ℝ) 1 → comparisonConditionalScale P.context.N delta P.context.E P.lam ≤ x →
      laplaceComparisonStrength P.context.d P.lam x ≤ (eta*c0)^3*x^2 →
      ∀r∈Icc (0:ℝ) 1,r ≤ C*x →
        laplaceComparisonStrength P.context.d P.lam r ≤
          eta^2*(actualChildCutoff (n+1) delta c0 P.context.d P.lam x)^2 ∧
        laplaceComparisonStrength P.context.d P.lam r*r ≤
          C*eta^3*(actualChildCutoff (n+1) delta c0 P.context.d P.lam x)^3 := by
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  have H:=actual_child_nonceiling_clocks_eventually m delta c0 1 (1/C0) eta C hc0 hc01
    zero_lt_one (one_div_pos.mpr hC0) heta heta1 hC hmargin
  filter_upwards [hs.eventually H] with n hn
  intro P x hx htarget hweak r hr hrC
  have hlo : (1/C0)*P.context.N^(-(2:ℝ)/3+m)*P.context.d ≤ P.context.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using P.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : P.context.E ≤ P.context.d^2/Real.sqrt (n+1:ℕ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr P.context.hN)).mpr (by simpa only [mul_comm] using P.hupper)
  have hax : Real.sqrt (n+1:ℕ)*P.context.E/P.context.d ≤ x :=
    (comparison_conditional_scale_ge_lower (by exact_mod_cast P.context.hn) hdelta.le
      P.context.hE P.context.hd P.hlam P.hld).trans htarget
  have hdirect : ((n+1:ℕ):ℝ)^(1+delta)*P.context.E^2 ≤
      laplaceComparisonStrength P.context.d P.lam x*x^2 := by
    have H:=comparison_radius_target_strength_size (by exact_mod_cast P.context.hn)
      hdelta.le P.context.hd P.hlam P.hld P.context.hE hup hx.1
      (C:=1) le_rfl hx.1 (by simp) htarget
    have he : P.context.N^(1+delta)=P.context.N^delta*P.context.N := by
      rw [show (1:ℝ)+delta=delta+1 by ring,Real.rpow_add P.context.hN,Real.rpow_one]
    simpa only [div_one,he] using H
  by_cases Hcase : (actualChildRadius c0 x)^2/Real.sqrt (n+1:ℕ) ≤
      ((n+1:ℕ):ℝ)^(-100*delta)*laplaceComparisonStrength P.context.d P.lam x*x^3
  · have ha : actualChildCutoff (n+1) delta c0 P.context.d P.lam x=c0*x := by
      unfold actualChildCutoff actualChildErrorBudget
      rw [min_eq_left Hcase]
      unfold actualChildRadius
      field_simp
    rw [ha]
    have hgap : laplaceComparisonStrength P.context.d P.lam x*x ≤ eta^3*(c0*x)^3 := by
      have H:=mul_le_mul_of_nonneg_right hweak hx.1.le
      nlinarith only [H]
    exact actual_child_clock_increments P.context.hd P.hlam P.hld hx (mul_pos hc0 hx.1)
      (mul_le_of_le_one_left hx.1.le hc01) heta.le heta1 hgap hC hr hrC
  · have hbudget : actualChildErrorBudget (n+1) delta c0 P.context.d P.lam x=
        ((n+1:ℕ):ℝ)^(-100*delta)*laplaceComparisonStrength P.context.d P.lam x*x^3 :=
      min_eq_right (le_of_not_ge Hcase)
    exact hn P.context.d P.lam x P.context.E P.context.hd P.hlam P.hld hx hlo hup hax
      (by simpa only [one_mul] using hdirect) hbudget r hr hrC

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
