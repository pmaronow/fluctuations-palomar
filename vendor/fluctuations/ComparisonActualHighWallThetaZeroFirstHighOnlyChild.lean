module

public import ComparisonActualHighWallThetaZeroFirstAllMassChild

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem high_gap_of_large_epsilon {c0:ℝ} (hc0:0<c0)
    (heps:M.data.T/4≤M.data.epsilon) (hd:M.data.d^2≤M.data.T/8)
    (hchild:(c0*M.xs)^2≤M.data.T/8) :
    ∀u∈Ico (0:ℝ) M.data.s,
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u+
          (c0*M.xs)^2 ≤
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b M.data.s-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha M.data.s := by
  intro u hu
  rw [M.data.theta_zero_changed_low_matrix M.lam M.hlam M.hld M.alpha hu.2]
  have H:=M.data.theta_zero_changed_high_matrix M.lam M.hlam M.hld M.alpha (le_refl M.data.s)
  linarith only [H,heps,hd,hchild,M.hld]

def highOnlyChildData {c0:ℝ} (hc0:0<c0)
    (hgap:∀u∈Ico (0:ℝ) M.data.s,
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u+
          (c0*M.xs)^2 ≤
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b M.data.s-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha M.data.s) :
    ActualHighOnlyComparisonData n delta := by
  let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  have had:=P.clockAdmissible M.alpha
  exact {
    E:=actualChildErrorBudget n delta c0 M.data.d M.lam M.xs
    d:=c0*M.xs
    s:=M.data.s
    b:=fun u=>P.b u-P.coefficient M.alpha u
    h:=fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u
    hn:=M.data.hn
    hE:=actual_child_budget_pos M.data.hN hc0 M.hlam M.hxs
    hd:=mul_pos hc0 M.hxs
    hs:=⟨M.data.hs.1.le,M.data.hs.2.trans (by norm_num)⟩
    hq:=M.data.hq
    hb:=had.1
    hh:=had.2.1
    hb0:=had.2.2.1 0 (by norm_num)
    hh0:=had.2.2.2 0 (by norm_num)
    hcut:=by
      have H:=hgap 0 ⟨le_rfl,M.data.hs.1⟩
      have Hb:=had.2.2.1 0 (by norm_num)
      linarith only [H,Hb]
    hcross:=hgap}

def highOnlyChildSweepCost {c0:ℝ} (hc0:0<c0)
    (hgap:∀u∈Ico (0:ℝ) M.data.s,
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u+
          (c0*M.xs)^2 ≤
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b M.data.s-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha M.data.s) : ℝ :=
  let child:=M.highOnlyChildData hc0 hgap
  omittedComparisonSweepCost zero_le_one ⟨M.data.hs.1.le,M.data.hs1⟩
    child.hc child.hk child.hkc child.hm child.hM n child.b child.h child.d ((c0*M.xs)^2)

theorem exists_high_only_child {c0:ℝ} (hc0:0<c0)
    (hgap:∀u∈Ico (0:ℝ) M.data.s,
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u+
          (c0*M.xs)^2 ≤
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b M.data.s-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha M.data.s) :
    ∃a:ActualShiftedParentChildCall n delta,
      a.context=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld ∧
      HEq a.optimizer M.shiftedMinimum ∧
      a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2 ∧
      a.childData.s=M.data.s ∧
      a.childData.b=(fun u=>(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u) ∧
      a.childData.h=(fun u=>(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).h u+
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u*
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).R M.alpha u) ∧
      a.err=M.highOnlyChildSweepCost hc0 hgap := by
  let child:=M.highOnlyChildData hc0 hgap
  have Hlam:(c0*M.xs)^2∈Icc (0:ℝ) (child.d^2):=
    ⟨(sq_pos_of_pos (mul_pos hc0 M.hxs)).le,le_rfl⟩
  obtain ⟨Q⟩:=child.exists_actual_minimum Hlam
  have Hcost:child.cost ((c0*M.xs)^2)=M.highOnlyChildSweepCost hc0 hgap:=rfl
  have Hsuccess:child.objective ((c0*M.xs)^2) Q.alpha ≤
      realOrderedSKPathPressure n child.b child.h 0+M.highOnlyChildSweepCost hc0 hgap := by
    change child.minimum ((c0*M.xs)^2)-realOrderedSKPathPressure n child.b child.h 0=_ at Hcost
    rw [Q.attained]
    linarith only [Hcost]
  let a:ActualShiftedParentChildCall n delta:={
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

theorem exists_fixed_margin_first_child {c0:ℝ} (hc0:0<c0)
    (hd:M.data.d^2≤M.data.T/8) (hchild:(c0*M.xs)^2≤M.data.T/8) :
    (∃a:ActualShiftedAllMassParentChildCall n delta,
      a.context=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld ∧
      HEq a.optimizer M.shiftedMinimum ∧
      a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2) ∨
    (∃a:ActualShiftedParentChildCall n delta,
      a.context=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld ∧
      HEq a.optimizer M.shiftedMinimum ∧
      a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2) := by
  rcases le_total M.data.epsilon (M.data.T/4) with heps|heps
  · obtain ⟨a,hcontext,hoptimizer,_,hr,hl,_⟩:=
      M.exists_all_mass_child hc0 (M.all_mass_child_room_of_small_epsilon hc0 heps hchild)
    exact Or.inl ⟨a,hcontext,hoptimizer,hr,hl⟩
  · obtain ⟨a,hcontext,hoptimizer,hr,hl,_⟩:=
      M.exists_high_only_child hc0 (M.high_gap_of_large_epsilon hc0 heps hd hchild)
    exact Or.inr ⟨a,hcontext,hoptimizer,hr,hl⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
