module

public import ComparisonActualHighWallShiftedParentData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace ActualHighWallOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}

abbrev macroChildNumerics (M:ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0:ℝ} (hc0:0 < c0):NativeChildBarrierParameters n delta:=
  (show NativeChildBarrierParameters n delta from {E:=M.data.E,d:=M.data.d,hn:=M.data.hn,hE:=M.data.hE,hd:=M.data.hd}).actualChild
    (sq_pos_of_pos M.data.hd) hc0 M.hxs

def macroHighOnlyChildSweepCost (M:ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0:ℝ} (hc0:0 < c0):ℝ:=
  let c:=M.macroChildNumerics hc0
  omittedComparisonSweepCost zero_le_one ⟨M.data.hs.1.le,M.data.hs1⟩ c.hc c.hk c.hkc c.hm c.hM
    n (M.data.b M.alpha) (M.data.h M.alpha) c.d ((c0*M.xs)^2)

theorem exists_actual_high_wall_macro_high_only_child
    (M:ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0:ℝ} (hc0:0 < c0) (hreserve:M.data.d^2+(c0*M.xs)^2 ≤ M.data.epsilon):
    ∃a:ActualShiftedParentChildCall n delta,
      a.context=M.data.shiftedParentData ∧ HEq a.optimizer M.shiftedParentMinimum ∧
      a.R=M.data.wallRadius M.alpha ∧ a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2 ∧
      a.childData.s=M.data.s ∧ a.childData.b=M.data.b M.alpha ∧ a.childData.h=M.data.h M.alpha ∧
      a.err=M.macroHighOnlyChildSweepCost hc0:=by
  have hE:0 < actualChildErrorBudget n delta c0 M.data.d (M.data.d^2) M.xs:=
    actual_child_budget_pos M.data.hN hc0 (sq_pos_of_pos M.data.hd) M.hxs
  have hd:0 < c0*M.xs:=mul_pos hc0 M.hxs
  let child:=M.data.highOnlyChildData M.alpha hE hd hreserve
  have Hlam:(c0*M.xs)^2∈Icc (0:ℝ) (child.d^2):=⟨(sq_pos_of_pos hd).le,le_rfl⟩
  obtain ⟨Q⟩:=child.exists_actual_minimum Hlam
  have Hsuccess:child.objective ((c0*M.xs)^2) Q.alpha ≤
      realOrderedSKPathPressure n child.b child.h 0+M.macroHighOnlyChildSweepCost hc0:=by
    have Hcost:child.cost ((c0*M.xs)^2)=M.macroHighOnlyChildSweepCost hc0:=rfl
    change child.minimum ((c0*M.xs)^2)-realOrderedSKPathPressure n child.b child.h 0=_ at Hcost
    rw [Q.attained]
    linarith
  have Hb:child.b=(fun u=>M.data.shiftedParentData.b u-
      M.data.shiftedParentData.coefficient M.shiftedParentMinimum.alpha u):=by
    change M.data.b M.alpha=(fun u=>wallBareMatrix M.data.T M.data.epsilon M.data.theta M.data.s u-
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u)
    rw [M.data.masked_coefficient_eq M.alpha]
    rfl
  have Hh:child.h=(fun u=>M.data.shiftedParentData.h u+
      M.data.shiftedParentData.coefficient M.shiftedParentMinimum.alpha u*
        M.data.shiftedParentData.R M.shiftedParentMinimum.alpha u):=by
    ext u
    change M.data.h M.alpha u=wallBareField M.data.T M.data.epsilon M.data.theta M.data.s M.data.tau M.data.d M.data.rmin u+
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u*M.data.wallRadius M.alpha u
    rw [congrFun (M.data.masked_field_coefficient_eq M.alpha) u]
    rfl
  let a:ActualShiftedParentChildCall n delta:={
    context:=M.data.shiftedParentData
    optimizer:=M.shiftedParentMinimum
    childData:=child
    childLam:=(c0*M.xs)^2
    hchildLam:=sq_pos_of_pos hd
    hchildLd:=le_rfl
    childOptimizer:=Q
    sameInitialMass:=rfl
    childBareMatrix:=Hb
    childBareField:=Hh
    err:=M.macroHighOnlyChildSweepCost hc0
    childSuccess:=Hsuccess}
  exact ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
