module

public import ComparisonNativeActualHistoryCutoffLedger
public import ComparisonActualHighWallInnovation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
variable {m delta C0 c0 : ℝ}

theorem eventually_actual_child_numeric_clock_increments_from_target
    (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    {eta C : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) (hC : 1 ≤ C)
    (hmargin : 0 < 9*m-298*delta) :
    ∀ᶠn : ℕ in atTop,∀d lam E x : ℝ,
      0<d → 0<lam → lam≤d^2 → 0<E →
      (1/C0)*(n:ℝ)^(-(2:ℝ)/3+m)*d≤E → E≤d^2/Real.sqrt (n:ℝ) →
      x∈Ioc (0:ℝ) 1 → comparisonConditionalScale (n:ℝ) delta E lam ≤ x →
      laplaceComparisonStrength d lam x ≤ (eta*c0)^3*x^2 →
      ∀r∈Icc (0:ℝ) 1,r ≤ C*x →
        laplaceComparisonStrength d lam r ≤
          eta^2*(actualChildCutoff n delta c0 d lam x)^2 ∧
        laplaceComparisonStrength d lam r*r ≤
          C*eta^3*(actualChildCutoff n delta c0 d lam x)^3 := by
  have H:=actual_child_nonceiling_clocks_eventually m delta c0 1 (1/C0) eta C hc0 hc01
    zero_lt_one (one_div_pos.mpr hC0) heta heta1 hC hmargin
  filter_upwards [H,eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro d lam E x hd hlam hld hE hlo hup hx htarget hweak r hr hrC
  have hN1 : (1:ℝ)≤(n:ℝ):=by exact_mod_cast hn1
  have hN : 0<(n:ℝ):=zero_lt_one.trans_le hN1
  have hax : Real.sqrt (n:ℕ)*E/d ≤ x :=
    (comparison_conditional_scale_ge_lower (by exact_mod_cast hn1) hdelta.le
      hE hd hlam hld).trans htarget
  have hdirect : ((n:ℕ):ℝ)^(1+delta)*E^2 ≤
      laplaceComparisonStrength d lam x*x^2 := by
    have H:=comparison_radius_target_strength_size (by exact_mod_cast hn1)
      hdelta.le hd hlam hld hE hup hx.1
      (C:=1) le_rfl hx.1 (by simp) htarget
    have he : (n:ℝ)^(1+delta)=(n:ℝ)^delta*(n:ℝ) := by
      rw [show (1:ℝ)+delta=delta+1 by ring,Real.rpow_add hN,Real.rpow_one]
    simpa only [div_one,he] using H
  by_cases Hcase : (actualChildRadius c0 x)^2/Real.sqrt (n:ℕ) ≤
      ((n:ℕ):ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3
  · have ha : actualChildCutoff n delta c0 d lam x=c0*x := by
      unfold actualChildCutoff actualChildErrorBudget
      rw [min_eq_left Hcase]
      unfold actualChildRadius
      field_simp
    rw [ha]
    have hgap : laplaceComparisonStrength d lam x*x ≤ eta^3*(c0*x)^3 := by
      have H:=mul_le_mul_of_nonneg_right hweak hx.1.le
      nlinarith only [H]
    exact actual_child_clock_increments hd hlam hld hx (mul_pos hc0 hx.1)
      (mul_le_of_le_one_left hx.1.le hc01) heta.le heta1 hgap hC hr hrC
  · have hbudget : actualChildErrorBudget n delta c0 d lam x=
        ((n:ℕ):ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3 :=
      min_eq_right (le_of_not_ge Hcase)
    exact hn d lam x E hd hlam hld hx hlo hup hax
      (by simpa only [one_mul] using hdirect) hbudget r hr hrC

end OAI.SKFluctuations.LaplaceWindowFormalization
