module

public import ComparisonNativeActualChildParameterGrowth
public import ComparisonNativeActualHistoryLowField

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000

theorem actual_parent_strength_radius_le_child_cutoff
    {n : ℕ} {delta c0 d lam x D : ℝ}
    (hN : 0<(n:ℝ)) (hc0 : 0<c0) (hd : 0<d) (hlam : 0<lam)
    (hld : lam≤d^2) (hdD : d≤D) (hx : 0<x)
    (hcx : c0≤Real.sqrt n*(n:ℝ)^(-100*delta)*x)
    (hcd : c0≤Real.sqrt n*(n:ℝ)^(-100*delta)*d) :
    lam*x ≤ max 1 (D^2/c0)*actualChildCutoff n delta c0 d lam x := by
  let q:=Real.sqrt n*(n:ℝ)^(-100*delta)
  let C:=max 1 (D^2/c0)
  have hq : 0<q := by dsimp [q];positivity
  have hC : 1≤C := le_max_left _ _
  have hCd : D^2≤C*c0 := (div_le_iff₀ hc0).mp (le_max_right _ _)
  have hlamD : lam≤D^2 := hld.trans (pow_le_pow_left₀ hd.le hdD 2)
  have he := laplaceComparisonStrength_pos d hlam x
  have hs : lam*x≤q*laplaceComparisonStrength d lam x*x^2/c0 := by
    apply (le_div_iff₀ hc0).mpr
    have hl:=laplaceComparisonStrength_lower hd hlam hx
    rcases min_le_iff.mp hl with hl|hl
    · have H1:=mul_le_mul_of_nonneg_left hcx hlam.le
      have H2:=mul_le_mul_of_nonneg_right hl (mul_nonneg hq.le hx.le)
      have H3:=mul_le_mul_of_nonneg_right (H1.trans H2) hx.le
      dsimp only [q] at H3 ⊢
      nlinarith only [H3]
    · have H1:=mul_le_mul_of_nonneg_left hcd hlam.le
      have H2:=mul_le_mul_of_nonneg_right hld (mul_nonneg hq.le hd.le)
      have H3:=mul_le_mul_of_nonneg_left ((div_le_iff₀ hx).mp hl) hq.le
      have H4 : lam*c0≤q*laplaceComparisonStrength d lam x*x := by
        calc
          _≤lam*(q*d) := H1
          _≤d^2*(q*d) := H2
          _=q*d^3 := by ring
          _≤_ := by nlinarith only [H3]
      nlinarith only [mul_le_mul_of_nonneg_right H4 hx.le]
  have hc : lam*x≤C*(c0*x) := by
    have H:=mul_le_mul_of_nonneg_right (hlamD.trans hCd) hx.le
    nlinarith only [H]
  change lam*x≤C*actualChildCutoff n delta c0 d lam x
  unfold actualChildCutoff actualChildErrorBudget actualChildRadius
  by_cases H : (c0*x)^2/Real.sqrt n≤(n:ℝ)^(-100*delta)*laplaceComparisonStrength d lam x*x^3
  · rw [min_eq_left H]
    convert hc using 1
    field_simp
  · rw [min_eq_right (le_of_not_ge H)]
    have Hmul:=mul_le_mul_of_nonneg_right hC
      (show 0≤q*laplaceComparisonStrength d lam x*x^2/c0 by positivity)
    simp only [one_mul] at Hmul
    apply hs.trans (Hmul.trans_eq _)
    dsimp [q]
    field_simp

theorem eventually_actual_parent_strength_radius_le_child_cutoff
    {m delta gamma c0 D : ℝ} (hgamma : 0<gamma) (hc0 : 0<c0)
    (hmargin : 100*delta<(1:ℝ)/3+m) :
    ∀ᶠn : ℕ in atTop,∀d lam E x : ℝ,
      0<d → 0<lam → lam≤d^2 → d≤D → 0<x →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d≤E → E≤d^2/Real.sqrt n →
      Real.sqrt n*E/d≤x →
      lam*x ≤ max 1 (D^2/c0)*actualChildCutoff n delta c0 d lam x := by
  have Hrate:=eventually_coefficient_rpow_le (c:=c0) (d:=gamma)
    (q:=0) (r:=(1:ℝ)/3+m-100*delta) hgamma (by linarith)
  filter_upwards [Hrate,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  intro d lam E x hd hlam hld hdD hx hlo hup hax
  have hN : 0<(n:ℝ) := by exact_mod_cast hnpos
  have hp:=comparison_parent_scale_lower_bounds hN hgamma hd hlo hup
  have Hscale (z : ℝ) (hz : gamma*(n:ℝ)^(-(1:ℝ)/6+m)≤z) :
      c0≤Real.sqrt n*(n:ℝ)^(-100*delta)*z := by
    have H:=mul_le_mul_of_nonneg_left hz
      (show 0≤Real.sqrt n*(n:ℝ)^(-100*delta) by positivity)
    have he : Real.sqrt n*(n:ℝ)^(-100*delta)*(gamma*(n:ℝ)^(-(1:ℝ)/6+m))=
        gamma*(n:ℝ)^((1:ℝ)/3+m-100*delta) := by
      rw [Real.sqrt_eq_rpow]
      calc
        _=gamma*((n:ℝ)^((1:ℝ)/2)*(n:ℝ)^(-100*delta)*(n:ℝ)^(-(1:ℝ)/6+m)) := by ring
        _=_ := by rw [←Real.rpow_add hN,←Real.rpow_add hN];congr 2;ring
    rw [he] at H
    have hn' : c0≤gamma*(n:ℝ)^((1:ℝ)/3+m-100*delta) := by
      simpa only [Real.rpow_zero,mul_one] using hn
    exact hn'.trans H
  exact actual_parent_strength_radius_le_child_cutoff hN hc0 hd hlam hld hdD hx
    (Hscale x (hp.2.2.trans hax)) (Hscale d hp.1)

end OAI.SKFluctuations.LaplaceWindowFormalization
