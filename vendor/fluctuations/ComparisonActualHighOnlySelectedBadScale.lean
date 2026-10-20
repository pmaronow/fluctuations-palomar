module

public import ComparisonActualHighOnlyOverlapMinimum
public import ComparisonNativeActualBadScaleSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {m delta cl cu Az C0 Ct D T lam : ℝ}

def selectedBadScaleMinimum (a : ActualHighOnlyComparisonData n delta)
    (optimizer : ActualHighOnlyComparisonMinimum a lam)
    (hlam : 0 < lam) (hld : lam ≤ a.d^2) (hdelta : 0 ≤ delta)
    (x : ℝ) (hx : 0 < x)
    (htarget : comparisonConditionalScale a.N delta a.E lam ≤ x)
    (hdD : a.d ≤ D) (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
    (htotal : ∀u∈Icc (0:ℝ) 1,a.h u+a.b u ≤ T)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct)
    (hregular : ∀r∈Icc (min (2*x) 1) 1,
      cl*r ≤ optimizer.alpha.val.val r ∧ optimizer.alpha.val.val r ≤ cu*r) :
    ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D T where
  data := a
  lam := lam
  hlam := hlam
  hld := hld
  optimizer := optimizer
  xs := x
  z := min (2*x) 1
  hxs := hx
  hscale := (comparison_conditional_scale_ge_lower (by exact_mod_cast (Nat.succ_le_iff.mpr a.hn : 1≤n)) hdelta a.hE a.hd hlam hld).trans htarget
  hz := ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  hzxs := (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hAz hx.le)
  hdD := hdD
  hupper := hupper
  hlower := hlower
  htest := by
    have H:=comparison_selected_scale_direct_test (by exact_mod_cast (Nat.succ_le_iff.mpr a.hn : 1≤n)) hdelta a.hE a.hd hlam hld hupper hx htarget
    have Hmul:=mul_le_mul_of_nonneg_right hCt
      (mul_nonneg (laplaceComparisonStrength_pos a.d hlam x).le (sq_nonneg x))
    exact H.trans (by simpa only [one_mul,mul_assoc] using Hmul)
  regular := hregular
  clockBudget := by
    have H:=a.total_clock_le optimizer.alpha ⟨hlam.le,hld⟩ htotal (by norm_num : (1:ℝ)∈Icc 0 1)
    have hb:=NNReal.coe_nonneg (a.bf optimizer.alpha lam 1)
    have hh:=NNReal.coe_nonneg (a.hf optimizer.alpha lam 0)
    linarith

theorem exists_selected_bad_scale_minimum_of_attained
    (a : ActualHighOnlyComparisonData n delta)
    (optimizer : ActualHighOnlyComparisonMinimum a lam)
    (hlam : 0 < lam) (hld : lam ≤ a.d^2) (hdelta : 0 ≤ delta)
    (hdD : a.d ≤ D) (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
    (htotal : ∀u∈Icc (0:ℝ) 1,a.h u+a.b u ≤ T)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct) (hcl : cl ≤ 1) (hcu : 1 ≤ cu)
    (hbad : ∃r∈Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
      optimizer.alpha.val.val r < cl*r ∨ cu*r < optimizer.alpha.val.val r) :
    ∃Q : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D T,
      Q.data=a ∧ Q.lam=lam ∧ HEq Q.optimizer optimizer ∧
      Q.xs∈Icc (comparisonConditionalScale a.N delta a.E lam) 1 ∧
      Q.z=min (2*Q.xs) 1 ∧
      (Q.alpha.val.val Q.xs < cl*Q.xs ∨ cu*Q.xs < Q.alpha.val.val Q.xs) := by
  have hA:=comparison_conditional_scale_pos (delta:=delta) a.hN a.hE hlam
  obtain ⟨x,hx,hbadx,hregular⟩:=comparison_exists_bad_scale_with_regular_outer optimizer.alpha.val.val
    hA hcl hcu optimizer.alpha.property.2.1 hbad
  have hx0 : 0 < x:=hA.trans_le hx.1
  let Q:=a.selectedBadScaleMinimum optimizer hlam hld hdelta x hx0 hx.1
    hdD hupper hlower htotal hAz hCt hregular
  exact ⟨Q,rfl,rfl,HEq.rfl,hx,rfl,hbadx⟩

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
