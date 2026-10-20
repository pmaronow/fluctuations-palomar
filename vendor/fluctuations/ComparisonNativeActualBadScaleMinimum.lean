module

public import ComparisonNativeActualBadScaleSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000
namespace NativeOverlapContext
variable {n : ℕ} {margin delta cl cu Az C0 Ct D T lam : ℝ}

def selectedBadScaleMinimum (c : NativeOverlapContext n delta)
    (alpha : c.Profile) (b h : ℝ → ℝ)
    (hlam : 0 < lam) (hld : lam ≤ c.d^2) (hdelta : 0 ≤ delta)
    (x : ℝ) (hx : 0<x)
    (htarget : comparisonConditionalScale c.N delta c.E lam≤x)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hminimum : ∀beta : c.Profile,
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam alpha ≤
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam beta)
    (hdD : c.d ≤ D) (hupper : Real.sqrt c.N*c.E ≤ c.d^2)
    (hlower : c.N^(-(2:ℝ)/3+margin)*c.d ≤ C0*c.E)
    (htotal : ∀u∈Icc (0:ℝ) 1,h u+b u ≤ T)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct)
    (hregular : ∀r∈Icc (min (2*x) 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) :
    NativeOverlapMinimum n margin delta cl cu Az C0 Ct D T where
  context := c
  lam := lam
  hlam := hlam
  hld := hld
  alpha := alpha
  b := b
  h := h
  hb := hb
  hlb := hlb
  hh := hh
  hh0 := hh0
  minimum := hminimum
  xs := x
  z := min (2*x) 1
  hxs := hx
  hscale := (comparison_conditional_scale_ge_lower (by exact_mod_cast c.hn)
    hdelta c.hE c.hd hlam hld).trans htarget
  hz := ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  hzxs := (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hAz hx.le)
  hdD := hdD
  hupper := hupper
  hlower := hlower
  htest := by
    have H := comparison_selected_scale_direct_test
      (by exact_mod_cast c.hn) hdelta c.hE c.hd hlam hld hupper hx htarget
    have Hmul := mul_le_mul_of_nonneg_right hCt
      (mul_nonneg (laplaceComparisonStrength_pos c.d hlam x).le (sq_nonneg x))
    exact H.trans (by simpa only [one_mul,mul_assoc] using Hmul)
  regular := hregular
  clockBudget := by
    have hr := comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM alpha 1
    have hg := (laplaceComparisonStrength_pos c.d hlam (c.R alpha 1)).le
    have hgb := (laplaceComparisonStrength_le c.d hlam.le (c.R alpha 1)).trans
      (hlb.trans (hb (by norm_num) (by norm_num) zero_le_one))
    have hh1 := hh0.trans (hh (by norm_num) (by norm_num) zero_le_one)
    have he := mul_le_mul_of_nonneg_left hr.2 hg
    have hbound : h 1+laplaceComparisonStrength c.d lam (c.R alpha 1)*c.R alpha 1 ≤ T := by
      linarith [htotal 1 (by norm_num)]
    rw [Real.coe_toNNReal _ (add_nonneg hh1 (mul_nonneg hg hr.1))]
    exact sub_le_self _ (NNReal.coe_nonneg _)|>.trans hbound

theorem exists_selected_bad_scale_minimum_of_attained
    (c : NativeOverlapContext n delta) (alpha : c.Profile) (b h : ℝ→ℝ)
    (hlam : 0 < lam) (hld : lam ≤ c.d^2) (hdelta : 0 ≤ delta)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam ≤ b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hattained : variableEndpointComparisonSweepObjective c.hc c.hk c.hkc c.hm c.hM
      n b h c.d lam alpha=variableEndpointComparisonSweepMinimum c.hc c.hk c.hkc c.hm c.hM
        n b h c.d lam)
    (hdD : c.d ≤ D) (hupper : Real.sqrt c.N*c.E ≤ c.d^2)
    (hlower : c.N^(-(2:ℝ)/3+margin)*c.d ≤ C0*c.E)
    (htotal : ∀u∈Icc (0:ℝ) 1,h u+b u ≤ T)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct) (hcl : cl ≤ 1) (hcu : 1 ≤ cu)
    (hbad : ∃r∈Icc (min (comparisonConditionalScale c.N delta c.E lam) 1) 1,
      alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) :
    ∃M : NativeOverlapMinimum n margin delta cl cu Az C0 Ct D T,
      M.context=c ∧ M.lam=lam ∧ HEq M.alpha alpha ∧ M.b=b ∧ M.h=h ∧ M.R=c.R alpha ∧
      M.xs∈Icc (comparisonConditionalScale c.N delta c.E lam) 1 ∧
      M.z=min (2*M.xs) 1 ∧
      (M.alpha.val.val M.xs < cl*M.xs ∨ cu*M.xs < M.alpha.val.val M.xs) := by
  have hA := comparison_conditional_scale_pos (delta := delta) c.hN c.hE hlam
  obtain ⟨x,hx,hbadx,hregular⟩ := comparison_exists_bad_scale_with_regular_outer alpha.val.val
    hA hcl hcu alpha.property.2.1 hbad
  have hx0 : 0 < x := hA.trans_le hx.1
  let M := c.selectedBadScaleMinimum alpha b h hlam hld hdelta x hx0 hx.1
    hb hlb hh hh0 (c.minimum_of_sweep_attained alpha b h hlam.le hb hlb hh hh0 hattained)
    hdD hupper hlower htotal hAz hCt hregular
  exact ⟨M,rfl,rfl,HEq.rfl,rfl,rfl,rfl,hx,rfl,hbadx⟩

end NativeOverlapContext
end OAI.SKFluctuations.LaplaceWindowFormalization
