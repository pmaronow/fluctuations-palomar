module

public import ComparisonActualHighOnlyMacroscopicChildFactory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualHighOnlyOverlapMinimum

private theorem radius_eq_of_parent_fields_with_budget
    {n : ℕ} {delta : ℝ}
    (a : ActualHighOnlyChildBarrierCall n delta)
    (c : ActualHighOnlyComparisonData n delta) {lam : ℝ}
    (M : ActualHighOnlyComparisonMinimum c lam)
    (hcontext : a.context=c) (hlam : a.lam=lam)
    (hoptimizer : HEq a.optimizer M) : a.R=c.R M.alpha := by
  cases a
  cases hcontext
  cases hlam
  cases hoptimizer
  rfl

theorem exists_actual_high_only_macro_child_at_parent_with_budget
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0<c0)
    (hroom : M.lam+(c0*M.xs)^2 ≤ M.b M.context.s)
    (hcross : ∀u∈Ico (0:ℝ) M.context.s,
      M.b u+M.lam+(c0*M.xs)^2 ≤ M.b M.context.s) :
    ∃a : ActualHighOnlyChildBarrierCall n delta,
      a.context=M.context ∧ a.lam=M.lam ∧ a.R=M.R ∧
      a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2 ∧
      a.childData.E=actualChildErrorBudget n delta c0 M.context.d M.lam M.xs ∧
      a.childData.s=M.context.s ∧
      a.childData.b=(fun u=>M.b u-M.coefficient u) ∧
      a.childData.h=(fun u=>M.h u+M.coefficient u*M.R u) ∧
      a.err=M.macroChildSweepCost hc0 := by
  have hE : 0 < actualChildErrorBudget n delta c0 M.context.d M.lam M.xs :=
    actual_child_budget_pos M.context.hN hc0 M.hlam M.hxs
  have hd : 0 < c0*M.xs := mul_pos hc0 M.hxs
  have hsuccess :
      (M.context.childData M.alpha M.lam_mem hE hd hroom hcross).cost
        ((c0*M.xs)^2) ≤ M.macroChildSweepCost hc0 := le_rfl
  obtain ⟨a,hcontext,hlam,hoptimizer,hdata,hchildLam,herr⟩ :=
    M.context.exists_child_barrier_call M.hlam M.hld M.optimizer
      hE hd hroom hcross hsuccess
  have hR := radius_eq_of_parent_fields_with_budget a M.context M.optimizer
    hcontext hlam hoptimizer
  refine ⟨a,hcontext,hlam,hR,?_,hchildLam,?_,?_,?_,?_,herr⟩
  · change a.childData.d=c0*M.xs
    rw [hdata]
    rfl
  · rw [hdata]
    rfl
  · rw [hdata]
    rfl
  · rw [hdata]
    rfl
  · rw [hdata]
    rfl

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
