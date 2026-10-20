module

public import ComparisonActualHighOnlyChildData
public import ComparisonActualHighOnlyOverlapMinimum
public import ComparisonNativeActualChildConstruction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

abbrev macroChildNumerics (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0 < c0) : NativeChildBarrierParameters n delta :=
  (show NativeChildBarrierParameters n delta from {
    E:=M.context.E,d:=M.context.d,hn:=M.context.hn,hE:=M.context.hE,hd:=M.context.hd}).actualChild M.hlam hc0 M.hxs

def macroChildSweepCost (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0 < c0) : ℝ :=
  let child := M.macroChildNumerics hc0
  omittedComparisonSweepCost zero_le_one ⟨M.context.hs.1,M.context.hs1⟩
    child.hc child.hk child.hkc child.hm child.hM n
    (fun u=>M.b u-M.coefficient u) (fun u=>M.h u+M.coefficient u*M.R u)
    child.d ((c0*M.xs)^2)

private theorem radius_eq_of_parent_fields
    (a : ActualHighOnlyChildBarrierCall n delta)
    (c : ActualHighOnlyComparisonData n delta) {lam : ℝ}
    (M : ActualHighOnlyComparisonMinimum c lam)
    (hcontext : a.context=c) (hlam : a.lam=lam) (hoptimizer : HEq a.optimizer M) : a.R=c.R M.alpha := by
  cases a
  cases hcontext
  cases hlam
  cases hoptimizer
  rfl

theorem exists_actual_high_only_macro_child_at_parent
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0 < c0)
    (hroom : M.lam+(c0*M.xs)^2 ≤ M.b M.context.s)
    (hcross : ∀u∈Ico (0:ℝ) M.context.s,M.b u+M.lam+(c0*M.xs)^2 ≤ M.b M.context.s) :
    ∃a : ActualHighOnlyChildBarrierCall n delta,
      a.context.E=M.context.E ∧ a.context.d=M.context.d ∧ a.lam=M.lam ∧ a.R=M.R ∧
      a.context.s=M.context.s ∧ a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2 ∧
      a.childData.s=M.context.s ∧
      a.childData.b=(fun u=>M.b u-M.coefficient u) ∧
      a.childData.h=(fun u=>M.h u+M.coefficient u*M.R u) ∧
      a.err=M.macroChildSweepCost hc0 := by
  have hE : 0 < actualChildErrorBudget n delta c0 M.context.d M.lam M.xs :=
    actual_child_budget_pos M.context.hN hc0 M.hlam M.hxs
  have hd : 0 < c0*M.xs := mul_pos hc0 M.hxs
  have hsuccess : (M.context.childData M.alpha M.lam_mem hE hd hroom hcross).cost ((c0*M.xs)^2) ≤
      M.macroChildSweepCost hc0 := by
    exact le_rfl
  obtain ⟨a,hcontext,hlam,hoptimizer,hdata,hchildLam,herr⟩ :=
    M.context.exists_child_barrier_call M.hlam M.hld M.optimizer hE hd hroom hcross hsuccess
  have hR := radius_eq_of_parent_fields a M.context M.optimizer hcontext hlam hoptimizer
  refine ⟨a,?_,?_,hlam,hR,?_,?_,hchildLam,?_,?_,?_,herr⟩
  · rw [hcontext]
  · rw [hcontext]
  · rw [hcontext]
  · change a.childData.d=c0*M.xs
    rw [hdata]
    rfl
  · rw [hdata]
    rfl
  · rw [hdata]
    rfl
  · rw [hdata]
    rfl

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
