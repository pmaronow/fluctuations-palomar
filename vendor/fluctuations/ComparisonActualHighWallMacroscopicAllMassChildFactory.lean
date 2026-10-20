module

public import ComparisonActualHighWallMacroscopicHighOnlyChildFactory
public import ComparisonActualShiftedAllMassZeroDataBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def macroAllMassChildSweepCost (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0<c0) : ℝ :=
  let c:=M.macroChildNumerics hc0
  variableEndpointComparisonSweepCost c.hc c.hk c.hkc c.hm c.hM n
    (M.data.b M.alpha) (M.data.h M.alpha) c.d ((c0*M.xs)^2)

theorem exists_actual_high_wall_macro_all_mass_child
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0<c0) (hroom : (c0*M.xs)^2≤M.data.b M.alpha 0) :
    ∃a : ActualShiftedAllMassParentChildCall n delta,
      a.context=M.data.shiftedParentData ∧ HEq a.optimizer M.shiftedParentMinimum ∧
      a.R=M.data.wallRadius M.alpha ∧ a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2 ∧
      (∀u,a.context.b u-a.coefficient u=M.data.b M.alpha u) ∧
      (∀u,a.context.h u+a.coefficient u*a.R u=M.data.h M.alpha u) ∧
      a.err=M.macroAllMassChildSweepCost hc0 := by
  let child:=M.macroChildNumerics hc0
  have HC:=M.data.admissible M.alpha
  have Hb : (fun u=>M.data.shiftedParentData.b u-
      M.data.shiftedParentData.coefficient M.shiftedParentMinimum.alpha u)=M.data.b M.alpha:=by
    change (fun u=>wallBareMatrix M.data.T M.data.epsilon M.data.theta M.data.s u-
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u)=M.data.b M.alpha
    rw [M.data.masked_coefficient_eq M.alpha]
    rfl
  have Hh : (fun u=>M.data.shiftedParentData.h u+
      M.data.shiftedParentData.coefficient M.shiftedParentMinimum.alpha u*
        M.data.shiftedParentData.R M.shiftedParentMinimum.alpha u)=M.data.h M.alpha:=by
    ext u
    change wallBareField M.data.T M.data.epsilon M.data.theta M.data.s M.data.tau M.data.d M.data.rmin u+
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u*M.data.wallRadius M.alpha u=M.data.h M.alpha u
    rw [congrFun (M.data.masked_field_coefficient_eq M.alpha) u]
    rfl
  obtain ⟨beta,hbeta,_⟩:=variableEndpointComparisonSweepMinimum_attained child.hc child.hk child.hkc child.hm child.hM
    n M.data.hn (M.data.b M.alpha) (M.data.h M.alpha) child.hd.ne'
    (sq_pos_of_pos (mul_pos hc0 M.hxs)).le hroom HC.1 HC.2.1 HC.2.2.2
    (comparisonCap_continuous _ _ _ _ _ _) (child.profile_nonempty M.data.hq)
  let a : ActualShiftedAllMassParentChildCall n delta:={
    context:=M.data.shiftedParentData
    optimizer:=M.shiftedParentMinimum
    childData:=child
    childLam:=(c0*M.xs)^2
    hchildLam:=sq_pos_of_pos (mul_pos hc0 M.hxs)
    hchildLd:=le_rfl
    childAlpha:=beta
    matrixRoom:=by
      rw [←congrFun Hb 0] at hroom
      exact hroom
    attained:=by
      rw [Hb,Hh]
      exact hbeta}
  refine ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact congrFun Hb
  · exact congrFun Hh
  · change variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM n
      _ _ child.d ((c0*M.xs)^2)=_
    rw [Hb,Hh]
    rfl

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
