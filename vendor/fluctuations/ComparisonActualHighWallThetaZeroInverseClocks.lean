module

public import ComparisonActualHighWallThetaZeroDirectSweep
public import ComparisonActualHighWallShiftedParentData

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
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

theorem theta_zero_coefficient_eq_original (alpha:a.Profile) (lam:ℝ) :
    omittedStrengthCoefficient a.d a.s
      (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha) lam =
    omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
      (laplaceComparisonStrength a.d lam)
      (laplaceComparisonStrength_contDiff a.d lam).continuous alpha) :=
  omittedStrengthCoefficient_eq_original a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM a.d lam alpha

theorem theta_zero_field_coefficient_eq_original (alpha:a.Profile) (lam:ℝ) :
    omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
      (fun r=>laplaceComparisonStrength a.d lam r*r)
      ((laplaceComparisonStrength_contDiff a.d lam).continuous.mul continuous_id) alpha) =
    fun u=>omittedStrengthCoefficient a.d a.s
      (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha) lam u*
      omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha u := by
  ext u
  by_cases hu:a.s ≤ u <;>
    simp [omittedStrengthCoefficient,omittedSweepQuantile,omittedExtension,
      IccExtend,constrainedCoefficient,constrainedQuantileMap,hu,Function.comp_def]

theorem theta_zero_inverse_clock_eq (alpha:a.Profile) (lam:ℝ) :
    (fun u=>(a.thetaZeroHighOnlyData.b u-
      omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
        (laplaceComparisonStrength a.d lam)
        (laplaceComparisonStrength_contDiff a.d lam).continuous alpha) u).toNNReal) =
      (fun u=>(a.thetaZeroHighOnlyData.b u-
        omittedStrengthCoefficient a.d a.s
          (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha) lam u).toNNReal) ∧
    (fun u=>(a.thetaZeroHighOnlyData.h u+
      omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
        (fun r=>laplaceComparisonStrength a.d lam r*r)
        ((laplaceComparisonStrength_contDiff a.d lam).continuous.mul continuous_id) alpha) u).toNNReal) =
      (fun u=>(a.thetaZeroHighOnlyData.h u+
        omittedStrengthCoefficient a.d a.s
          (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha) lam u*
          omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha u).toNNReal) := by
  rw [←a.theta_zero_coefficient_eq_original alpha lam,
    a.theta_zero_field_coefficient_eq_original alpha lam]
  exact ⟨rfl,rfl⟩

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
