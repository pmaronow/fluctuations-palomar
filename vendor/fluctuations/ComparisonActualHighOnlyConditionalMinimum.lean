module

public import ComparisonActualHighOnlyOverlapMinimum
public import ComparisonNativeActualConditionalMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {m delta cl cu C0 D T lam : ℝ}

def conditionalMinimum (a : ActualHighOnlyComparisonData n delta)
    (optimizer : ActualHighOnlyComparisonMinimum a lam)
    (hlam : 0 < lam) (hld : lam ≤ a.d^2) (hdelta : 0 ≤ delta)
    (hdD : a.d ≤ D) (hupper : Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower : a.N^(-(2 : ℝ)/3+m)*a.d ≤ C0*a.E)
    (htotal : ∀ u ∈ Icc (0 : ℝ) 1,a.h u+a.b u ≤ T)
    (hregular : ∀ r ∈ Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
      cl*r ≤ optimizer.alpha.val.val r ∧ optimizer.alpha.val.val r ≤ cu*r) :
    ActualHighOnlyOverlapMinimum n m delta cl cu 1 C0 1 D T where
  data := a
  lam := lam
  hlam := hlam
  hld := hld
  optimizer := optimizer
  xs := comparisonConditionalScale a.N delta a.E lam
  z := min (comparisonConditionalScale a.N delta a.E lam) 1
  hxs := comparison_conditional_scale_pos a.hN a.hE hlam
  hscale := comparison_conditional_scale_ge_lower (by exact_mod_cast a.hn)
    hdelta a.hE a.hd hlam hld
  hz := ⟨le_min (comparison_conditional_scale_pos a.hN a.hE hlam).le zero_le_one,
    min_le_right _ _⟩
  hzxs := by simpa only [one_mul] using min_le_left (comparisonConditionalScale a.N delta a.E lam) 1
  hdD := hdD
  hupper := hupper
  hlower := hlower
  htest := by
    simpa only [one_mul] using comparison_conditional_scale_direct_test
      (by exact_mod_cast a.hn) hdelta a.hE a.hd hlam hld hupper
  regular := hregular
  clockBudget := by
    have H := a.total_clock_le optimizer.alpha ⟨hlam.le,hld⟩ htotal (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    have Hb := NNReal.coe_nonneg (a.bf optimizer.alpha lam 1)
    have Hh := NNReal.coe_nonneg (a.hf optimizer.alpha lam 0)
    linarith

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
