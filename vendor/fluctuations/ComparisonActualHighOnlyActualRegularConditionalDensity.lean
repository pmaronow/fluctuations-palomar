module

public import ComparisonActualHighOnlyRegularConditionalDensity
public import ComparisonActualHighOnlyConditionalMinimum

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyComparisonData
variable {m delta cl cu C0 D T:ℝ}

theorem eventually_actual_regular_conditional_original_density_high_only
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hclcu:cl ≤ cu) (hC0:0 < C0) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyComparisonData (n+1) delta) (lam:ℝ)
      (optimizer:ActualHighOnlyComparisonMinimum a lam),
      0 < lam → lam ≤ a.d^2 → a.d ≤ D → a.d ≤ 1 →
      Real.sqrt a.N*a.E ≤ a.d^2 → a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E →
      (∀u∈Icc (0:ℝ) 1,a.h u+a.b u ≤ T) →
      (∀r∈Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
        cl*r ≤ optimizer.alpha.val.val r ∧ optimizer.alpha.val.val r ≤ cu*r) →
      a.s ≤ 1/4 → a.s ≤ comparisonConditionalScale a.N delta a.E lam →
      NativePullbackClockRegularity optimizer.alpha.val.val a.b a.h 0 1 →
      a.originalSweepDensity lam optimizer.alpha ≤ a.N^(10*delta)*a.E := by
  have HD:=ActualHighOnlyOverlapMinimum.eventually_actual_regular_conditional_density_high_only
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=1) (C0:=C0) (Ct:=1) (D:=D) (Bclock:=T)
    hm hdelta hroom hcl hcu hclcu (by norm_num) hC0 (by norm_num)
  filter_upwards [HD] with n hn
  intro a lam optimizer hlam hld hdD hd1 hupper hlower htotal hregular hs hsA hclock
  let M:=a.conditionalMinimum optimizer hlam hld hdelta.le hdD hupper hlower htotal hregular
  exact hn M hd1 hs hsA rfl hclock

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
