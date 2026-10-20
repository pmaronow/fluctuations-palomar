module

public import ComparisonActualHighWallThetaZeroFirstHighOnlyChild

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem exists_literal_high_only_first_child_call
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0 < c0)
    (hgap : ∀u∈Ico (0:ℝ) M.data.s,
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u+
          (c0*M.xs)^2 ≤
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b M.data.s-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha M.data.s) :
    ∃a : ActualShiftedParentChildCall n delta,
      a.context=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld ∧
      HEq a.optimizer M.shiftedMinimum ∧
      a.R=M.data.wallRadius M.alpha ∧
      a.childData=M.highOnlyChildData hc0 hgap ∧
      a.childRadius=c0*M.xs ∧
      a.childLam=(c0*M.xs)^2 ∧
      a.childData.E=actualChildErrorBudget n delta c0 M.data.d M.lam M.xs ∧
      a.err=M.highOnlyChildSweepCost hc0 hgap := by
  let child := M.highOnlyChildData hc0 hgap
  have Hlam : (c0*M.xs)^2∈Icc (0:ℝ) (child.d^2) :=
    ⟨(sq_pos_of_pos (mul_pos hc0 M.hxs)).le,le_rfl⟩
  obtain ⟨Q⟩ := child.exists_actual_minimum Hlam
  have Hcost : child.cost ((c0*M.xs)^2)=M.highOnlyChildSweepCost hc0 hgap := rfl
  have Hsuccess : child.objective ((c0*M.xs)^2) Q.alpha ≤
      realOrderedSKPathPressure n child.b child.h 0+
        M.highOnlyChildSweepCost hc0 hgap := by
    change child.minimum ((c0*M.xs)^2)-
      realOrderedSKPathPressure n child.b child.h 0=_ at Hcost
    rw [Q.attained]
    linarith only [Hcost]
  let a : ActualShiftedParentChildCall n delta := {
    context:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
    optimizer:=M.shiftedMinimum
    childData:=child
    childLam:=(c0*M.xs)^2
    hchildLam:=sq_pos_of_pos (mul_pos hc0 M.hxs)
    hchildLd:=le_rfl
    childOptimizer:=Q
    sameInitialMass:=rfl
    childBareMatrix:=rfl
    childBareField:=rfl
    err:=M.highOnlyChildSweepCost hc0 hgap
    childSuccess:=Hsuccess}
  exact ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
