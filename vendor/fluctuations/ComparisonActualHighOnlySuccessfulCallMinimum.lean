module

public import ComparisonActualHighOnlySuccessfulChildMinimum
public import ComparisonActualHighOnlyChildBarrierCall

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set
set_option autoImplicit false
namespace ActualHighOnlyChildBarrierCall
variable {n : ℕ} {delta : ℝ}

private theorem cast_minimum_alpha
    {c : ActualHighOnlyComparisonData n delta} {lam lam' : ℝ}
    (h : lam=lam') (q : ActualHighOnlyComparisonMinimum c lam) :
    (h ▸ q).alpha=q.alpha := by
  cases h
  rfl

theorem exists_successful_minimum
    (a : ActualHighOnlyChildBarrierCall n delta)
    {m cl cu C0 c0 x C T Dchild : ℝ}
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hx : 0 < x)
    (hcl : 0 < cl) (hcu : 0 < cu) (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu) (hC : 1 ≤ C)
    (hd : a.childRadius = c0*x) (hfull : a.childLam = (a.childRadius)^2)
    (hdD : a.childRadius ≤ Dchild)
    (hupper : Real.sqrt (n:ℝ)*a.childData.E ≤ a.childRadius^2)
    (hlower : (n:ℝ)^(-(2:ℝ)/3+m)*a.childRadius ≤ C0*a.childData.E)
    (htotal : ∀u∈Icc (0:ℝ) 1,a.childData.h u+a.childData.b u ≤ T)
    (hquantile : ∀u∈Icc (C*x) 1,u/(4*cu) ≤ a.Z u ∧ a.Z u ≤ 4*u/cl) :
    ∃Q : ActualHighOnlyOverlapMinimum n m delta (cl/4) (4*cu) (4*C/cl)
      C0 1 Dchild T,
      Q.context = a.childData ∧ Q.R = a.Z ∧ Q.xs = x ∧ Q.lam = a.childLam := by
  have hfull' : a.childLam = a.childData.d^2 := hfull
  let optimizer : ActualHighOnlyComparisonMinimum a.childData (a.childData.d^2) :=
    hfull' ▸ a.childOptimizer
  have hoptimizerAlpha : optimizer.alpha=a.childOptimizer.alpha :=
    cast_minimum_alpha hfull' a.childOptimizer
  let Q := a.childData.successfulChildMinimum hc0 hc01 hx hcl hcu hcl1 hcu1 hC
    optimizer hd hdD hupper hlower htotal (by
      intro u hu
      simpa only [hoptimizerAlpha, ActualHighOnlyChildBarrierCall.Z] using hquantile u hu)
  refine ⟨Q,rfl,?_,rfl,?_⟩
  · change a.childData.R optimizer.alpha=a.Z
    rw [hoptimizerAlpha]
  · exact hfull'.symm

end ActualHighOnlyChildBarrierCall
end OAI.SKFluctuations.LaplaceWindowFormalization
