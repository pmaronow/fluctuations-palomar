module

public import ComparisonNativeActualConditionalMinimum
public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem comparison_selected_scale_direct_test
    {N delta E d lam x : ℝ} (hN : 1≤N) (hdelta : 0≤delta)
    (hE : 0<E) (hd : 0<d) (hlam : 0<lam) (hld : lam≤d^2)
    (hupper : Real.sqrt N*E≤d^2) (hx : 0<x)
    (htarget : comparisonConditionalScale N delta E lam≤x) :
    N*E^2≤laplaceComparisonStrength d lam x*x^2 := by
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hup : E≤d^2/Real.sqrt N := (le_div_iff₀ (Real.sqrt_pos.mpr hNp)).mpr
    (by simpa only [mul_comm] using hupper)
  have H:=comparison_radius_target_strength_size hN hdelta hd hlam hld hE hup hx
    (C:=1) le_rfl hx (by simp) htarget
  have Hbase:=mul_le_mul_of_nonneg_right (Real.one_le_rpow hN hdelta)
    (show 0≤N*E^2 by positivity)
  apply le_trans _ (by simpa only [div_one] using H)
  simpa only [one_mul,mul_assoc] using Hbase

namespace NativeOverlapContext
variable {n : ℕ} {margin delta cl cu C0 D T lam : ℝ}

def selectedScaleMinimum (c : NativeOverlapContext n delta)
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
    (hregular : ∀r∈Icc (min x 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) :
    NativeOverlapMinimum n margin delta cl cu 1 C0 1 D T where
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
  z := min x 1
  hxs := hx
  hscale := (comparison_conditional_scale_ge_lower (by exact_mod_cast c.hn)
    hdelta c.hE c.hd hlam hld).trans htarget
  hz := ⟨le_min hx.le zero_le_one,
    min_le_right _ _⟩
  hzxs := by
    simpa only [one_mul] using min_le_left x 1
  hdD := hdD
  hupper := hupper
  hlower := hlower
  htest := by
    simpa only [one_mul] using comparison_selected_scale_direct_test
      (by exact_mod_cast c.hn) hdelta c.hE c.hd hlam hld hupper hx htarget
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

theorem selectedScaleMinimum_data (c : NativeOverlapContext n delta)
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
    (hregular : ∀r∈Icc (min x 1) 1,
      cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) :
    let M:=c.selectedScaleMinimum alpha b h hlam hld hdelta x hx htarget
      hb hlb hh hh0 hminimum hdD hupper hlower htotal hregular
    M.context=c ∧ M.lam=lam ∧ HEq M.alpha alpha ∧ M.b=b ∧ M.h=h ∧
      M.xs=x ∧ M.z=min x 1 ∧ M.R=c.R alpha := by
  exact ⟨rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl⟩

end NativeOverlapContext
end OAI.SKFluctuations.LaplaceWindowFormalization
