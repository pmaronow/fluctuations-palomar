module

public import ComparisonActualHighWallThetaZeroVariableStrength

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

def thetaZeroWallValue (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2):ℝ:=
  sInf (Set.range (a.thetaZeroShiftedParentData lam hlam hld).objective)

theorem theta_zero_wall_value_attained (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2)
    (P:ActualShiftedParentMinimum (a.thetaZeroShiftedParentData lam hlam hld)) :
    a.thetaZeroWallValue lam hlam hld=(a.thetaZeroShiftedParentData lam hlam hld).objective P.alpha := by
  apply IsLeast.csInf_eq
  refine ⟨Set.mem_range_self P.alpha,?_⟩
  rintro _ ⟨gamma,rfl⟩
  exact P.minimum gamma

theorem theta_zero_full_objective_eq_original_wall (gamma:a.Profile) :
    (a.thetaZeroShiftedParentData (a.d^2) (sq_pos_of_pos a.hd) le_rfl).objective gamma=
      wallObjective a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
        a.T a.epsilon 0 a.tau a.d n 0 gamma := by
  have hfield:wallBareField a.T a.epsilon 0 a.s a.tau a.d a.rmin=(fun _=>0):=by
    funext u
    simp only [wallBareField,zero_mul,ite_self]
  simp only [wallObjective,zero_mul,zero_div,add_zero,hfield]
  exact omittedComparisonSweepObjective_eq_inverse a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM
    n (wallBareMatrix a.T a.epsilon 0 a.s) (fun _=>0) a.d (a.d^2) gamma

theorem theta_zero_full_value_eq_original_wall :
    a.thetaZeroWallValue (a.d^2) (sq_pos_of_pos a.hd) le_rfl=
      wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
        a.T a.epsilon a.tau a.d n 0 0 := by
  unfold thetaZeroWallValue wallMinimumValue
  congr 1
  apply congrArg Set.range
  funext gamma
  exact a.theta_zero_full_objective_eq_original_wall gamma

theorem exists_theta_zero_cap_lift_minimum_comparison (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2) :
    ∃Q:ActualHighOnlyComparisonMinimum a.thetaZeroHighOnlyData lam,
    ∃gamma:a.Profile,(∀u∈Icc a.s 1,
      gamma.val.val (a.capLiftRadius Q.alpha u)=u ∧
      0 ≤ a.capLiftRadius Q.alpha u-a.zeroOriginRadius Q.alpha u ∧
      a.capLiftRadius Q.alpha u-a.zeroOriginRadius Q.alpha u ≤ a.rmin) ∧
      a.thetaZeroWallValue lam hlam hld ≤ a.thetaZeroHighOnlyData.minimum lam+
        a.thetaZeroCapLiftPressurePad lam hlam hld Q.alpha gamma := by
  obtain ⟨P⟩:=a.theta_zero_shifted_minimum_attained lam hlam hld
  obtain ⟨Q⟩:=a.thetaZeroHighOnlyData.exists_actual_minimum ⟨hlam.le,hld⟩
  obtain ⟨gamma,Hgamma,Hmin⟩:=a.theta_zero_actual_minimum_le_cap_lift_with_literal_pad lam hlam hld P Q
  refine ⟨Q,gamma,Hgamma,?_⟩
  rw [a.theta_zero_wall_value_attained lam hlam hld P]
  exact Hmin

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
