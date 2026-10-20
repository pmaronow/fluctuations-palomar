module

public import ComparisonActualHighWallThetaZeroMinimumComparison
public import ComparisonNativeActualChildBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

abbrev thetaZeroSweepCost : ℝ → ℝ :=
  omittedComparisonSweepCost a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM
    n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d

def thetaZeroOriginalSweepDensity (lam : ℝ) (alpha : a.Profile) : ℝ :=
  let R := omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
  let e := omittedStrengthCoefficient a.d a.s R lam
  let bf := fun u => (a.thetaZeroHighOnlyData.b u-e u).toNNReal
  let hf := fun u => (a.thetaZeroHighOnlyData.h u+e u*R u).toNNReal
  ∫u in (0:ℝ)..1,e u*((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
    (orderedPathS n bf hf u-R u)^2)

theorem theta_zero_objective_eq_omitted (lam : ℝ) (hlam : 0 < lam)
    (hld : lam ≤ a.d^2) (alpha : a.Profile) :
    (a.thetaZeroShiftedParentData lam hlam hld).objective alpha =
      omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
        a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha := by
  rfl

theorem theta_zero_wall_value_eq_omitted (lam : ℝ) (hlam : 0 < lam)
    (hld : lam ≤ a.d^2) :
    a.thetaZeroWallValue lam hlam hld =
      omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
        a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam := by
  unfold thetaZeroWallValue omittedComparisonSweepMinimum
  congr 1

theorem theta_zero_wall_value_eq_bare_pressure_add_cost
    (lam : ℝ) (hlam : 0 < lam) (hld : lam ≤ a.d^2) :
    a.thetaZeroWallValue lam hlam hld =
      realOrderedSKPathPressure n a.thetaZeroHighOnlyData.b
        a.thetaZeroHighOnlyData.h 0+a.thetaZeroSweepCost lam := by
  rw [a.theta_zero_wall_value_eq_omitted lam hlam hld]
  unfold thetaZeroSweepCost omittedComparisonSweepCost
  ring

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
