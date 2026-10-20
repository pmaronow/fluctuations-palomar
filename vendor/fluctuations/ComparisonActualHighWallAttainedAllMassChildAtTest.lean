module

public import ComparisonActualHighWallMacroscopicAllMassChildFactory

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
abbrev allMassChildNumericsAtTest
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0 < c0) (hx : 0 < x) : NativeChildBarrierParameters n delta :=
  (show NativeChildBarrierParameters n delta from {E:=M.data.E,d:=M.data.d,hn:=M.data.hn,hE:=M.data.hE,hd:=M.data.hd}).actualChild
    (sq_pos_of_pos M.data.hd) hc0 hx

def allMassChildSweepCostAtTest
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0 < c0) (hx : 0 < x) : ℝ :=
  let c:=M.allMassChildNumericsAtTest hc0 hx
  variableEndpointComparisonSweepCost c.hc c.hk c.hkc c.hm c.hM n
    (M.data.b M.alpha) (M.data.h M.alpha) c.d ((c0*x)^2)

theorem exists_attained_all_mass_child_at_test
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0<c0) (hx : 0<x) (hroom : (c0*x)^2≤M.data.b M.alpha 0) :
    ∃a : ActualShiftedAllMassParentChildCall n delta,
      a.context=M.data.shiftedParentData ∧ HEq a.optimizer M.shiftedParentMinimum ∧
      a.R=M.data.wallRadius M.alpha ∧ a.childData=M.allMassChildNumericsAtTest hc0 hx ∧
      a.childRadius=c0*x ∧ a.childLam=(c0*x)^2 ∧
      a.childData.E=actualChildErrorBudget n delta c0 M.data.d (M.data.d^2) x ∧
      (∀u,a.context.b u-a.coefficient u=M.data.b M.alpha u) ∧
      (∀u,a.context.h u+a.coefficient u*a.R u=M.data.h M.alpha u) ∧
      a.err=M.allMassChildSweepCostAtTest hc0 hx := by
  let child:=M.allMassChildNumericsAtTest hc0 hx
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
    (sq_pos_of_pos (mul_pos hc0 hx)).le hroom HC.1 HC.2.1 HC.2.2.2
    (comparisonCap_continuous _ _ _ _ _ _) (child.profile_nonempty M.data.hq)
  let a : ActualShiftedAllMassParentChildCall n delta:={
    context:=M.data.shiftedParentData
    optimizer:=M.shiftedParentMinimum
    childData:=child
    childLam:=(c0*x)^2
    hchildLam:=sq_pos_of_pos (mul_pos hc0 hx)
    hchildLd:=le_rfl
    childAlpha:=beta
    matrixRoom:=by
      rw [←congrFun Hb 0] at hroom
      exact hroom
    attained:=by
      rw [Hb,Hh]
      exact hbeta}
  refine ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact congrFun Hb
  · exact congrFun Hh
  · change variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM n
      _ _ child.d ((c0*x)^2)=_
    rw [Hb,Hh]
    rfl

theorem allMassChildSweepCostAtTest_at_parent
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0 < c0) :
    M.allMassChildSweepCostAtTest hc0 M.hxs=M.macroAllMassChildSweepCost hc0 := rfl

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
