module

public import ComparisonNativeActualSuccessfulChildMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

def macroChildSweepCost {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 : ℝ} (hc0 : 0 < c0) : ℝ :=
  let child:=M.context.toChildBarrierParameters.actualChild M.hlam hc0 M.hxs
  variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM n
    (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
    (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
    child.d ((c0*M.xs)^2)

theorem exists_actual_macro_child_at_parent {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 xlo T : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hcl : 0 < cl) (hcu : 0 < cu) (hxlo : 0 < xlo)
    (hxs : M.xs∈Icc xlo 1) (hroom : M.lam+(c0*M.xs)^2≤M.b 0)
    (hq : 2≤(n:ℝ)^delta)
    (hlower : (n:ℝ)^(-(2:ℝ)/3+m)*(c0*M.xs)≤
      C0*actualChildErrorBudget n delta c0 M.context.d M.lam M.xs)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T) :
    ∃Q : NativeOverlapMinimum n m delta (cl/4) (4*cu) (4*(2/xlo)/cl) C0 1 1 T,
    ∃a : NativeChildBarrierCall n delta,
      Q.context.d=c0*M.xs ∧ Q.lam=(c0*M.xs)^2 ∧ Q.xs=M.xs ∧
      Q.b=(fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)) ∧
      Q.h=(fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u) ∧
      a.context.E=M.context.E ∧ a.context.d=M.context.d ∧ a.lam=M.lam ∧ a.R=M.R ∧
      a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2 ∧ a.Z=Q.R ∧ a.err=M.macroChildSweepCost hc0 := by
  obtain ⟨beta,a,hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr,hattained⟩ :=
    exists_actual_child_attained M hc0 M.hxs hroom hq
  have hdD : c0*M.xs≤1 :=
    (mul_le_mul_of_nonneg_left hxs.2 hc0.le).trans (by simpa using hc01)
  let Q := actualSuccessfulChildMinimum M hc0 hc01 M.hxs hcl hcu (show 0≤2/xlo by positivity)
    beta hroom hattained hdD hlower htotal
    (M.actual_successful_child_terminal_quantile hc0 M.hxs hxlo hxs.1 beta)
  refine ⟨Q,a,rfl,rfl,rfl,rfl,rfl,?_,?_,hlam,hR,hd,hl,hZ,he⟩
  · rw [hcontext];rfl
  · rw [hcontext];rfl

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
