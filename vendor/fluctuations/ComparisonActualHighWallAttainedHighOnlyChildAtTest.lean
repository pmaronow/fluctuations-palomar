module

public import ComparisonActualHighWallMacroscopicHighOnlyChildFactory

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

def highOnlyChildSweepCostAtTest
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0 < c0) (hx : 0 < x)
    (hreserve : M.data.d^2+(c0*x)^2 ≤ M.data.epsilon) : ℝ :=
    (M.actualHighOnlyChild hc0 hx hreserve).cost ((c0*x)^2)

theorem exists_attained_high_only_child_at_test
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0 < c0) (hx : 0 < x)
    (hreserve : M.data.d^2+(c0*x)^2 ≤ M.data.epsilon) :
    ∃a : ActualShiftedParentChildCall n delta,
      a.context=M.data.shiftedParentData ∧ HEq a.optimizer M.shiftedParentMinimum ∧
      a.R=M.data.wallRadius M.alpha ∧ a.childData=M.actualHighOnlyChild hc0 hx hreserve ∧
      a.childRadius=c0*x ∧ a.childLam=(c0*x)^2 ∧
      a.childData.E=actualChildErrorBudget n delta c0 M.data.d (M.data.d^2) x ∧
      a.childData.s=M.data.s ∧ a.childData.b=M.data.b M.alpha ∧ a.childData.h=M.data.h M.alpha ∧
      a.err=M.highOnlyChildSweepCostAtTest hc0 hx hreserve := by
  let child := M.actualHighOnlyChild hc0 hx hreserve
  have hd : 0 < c0*x := mul_pos hc0 hx
  have Hlam : (c0*x)^2∈Icc (0:ℝ) (child.d^2) := ⟨(sq_pos_of_pos hd).le,le_rfl⟩
  obtain ⟨Q⟩ := child.exists_actual_minimum Hlam
  have Hsuccess : child.objective ((c0*x)^2) Q.alpha ≤
      realOrderedSKPathPressure n child.b child.h 0+M.highOnlyChildSweepCostAtTest hc0 hx hreserve := by
    change child.objective ((c0*x)^2) Q.alpha ≤
      realOrderedSKPathPressure n child.b child.h 0+
        (child.minimum ((c0*x)^2)-realOrderedSKPathPressure n child.b child.h 0)
    rw [Q.attained]
    linarith
  have Hb : child.b=(fun u=>M.data.shiftedParentData.b u-
      M.data.shiftedParentData.coefficient M.shiftedParentMinimum.alpha u) := by
    change M.data.b M.alpha=(fun u=>wallBareMatrix M.data.T M.data.epsilon M.data.theta M.data.s u-
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u)
    rw [M.data.masked_coefficient_eq M.alpha]
    rfl
  have Hh : child.h=(fun u=>M.data.shiftedParentData.h u+
      M.data.shiftedParentData.coefficient M.shiftedParentMinimum.alpha u*
        M.data.shiftedParentData.R M.shiftedParentMinimum.alpha u) := by
    ext u
    change M.data.h M.alpha u=wallBareField M.data.T M.data.epsilon M.data.theta M.data.s M.data.tau M.data.d M.data.rmin u+
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u*M.data.wallRadius M.alpha u
    rw [congrFun (M.data.masked_field_coefficient_eq M.alpha) u]
    rfl
  let a : ActualShiftedParentChildCall n delta := {
    context:=M.data.shiftedParentData
    optimizer:=M.shiftedParentMinimum
    childData:=child
    childLam:=(c0*x)^2
    hchildLam:=sq_pos_of_pos hd
    hchildLd:=le_rfl
    childOptimizer:=Q
    sameInitialMass:=rfl
    childBareMatrix:=Hb
    childBareField:=Hh
    err:=M.highOnlyChildSweepCostAtTest hc0 hx hreserve
    childSuccess:=Hsuccess }
  exact ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem highOnlyChildSweepCostAtTest_at_parent
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0 < c0)
    (hreserve : M.data.d^2+(c0*M.xs)^2 ≤ M.data.epsilon) :
    M.highOnlyChildSweepCostAtTest hc0 M.hxs hreserve=M.macroHighOnlyChildSweepCost hc0 := rfl

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
