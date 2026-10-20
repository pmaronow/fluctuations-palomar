module

public import ComparisonActualHighOnlySuccessfulCallMinimum
public import ComparisonActualHighOnlyWeakenConstants

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualHighOnlyChildBarrierCall

theorem exists_regular_successful_child_sequence
    {m delta cl cu C0 c0 C T Dchild Ctchild : ℝ}
    (hc0 : 0<c0) (hc01 : c0≤1) (hcl : 0<cl) (hcu : 0<cu)
    (hcl1 : cl≤1) (hcu1 : 1≤cu) (hC : 1≤C)
    (hCt : 1≤Ctchild)
    (dim : ℕ→ℕ)
    (a : (n:ℕ)→ActualHighOnlyChildBarrierCall (dim n+1) delta)
    (x : ℕ→ℝ) (hx : ∀n,0<x n)
    (hd : ∀n,(a n).childRadius=c0*x n)
    (hfull : ∀n,(a n).childLam=((a n).childRadius)^2)
    (hdD : ∀n,(a n).childRadius≤Dchild)
    (hupper : ∀n,Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E≤
      (a n).childRadius^2)
    (hlower : ∀n,((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*
      (a n).childRadius≤C0*(a n).childData.E)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,
      (a n).childData.h u+(a n).childData.b u≤T)
    (hquantile : ∀n,∀u∈Icc (C*x n) 1,
      u/(4*cu)≤(a n).Z u ∧ (a n).Z u≤4*u/cl) :
    ∃Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
        m delta (cl/4) (4*cu) (4*C/cl) C0 Ctchild Dchild T,
      ∀n,(Q n).context=(a n).childData ∧ (Q n).R=(a n).Z ∧
        (Q n).xs=x n ∧ (Q n).lam=(a n).childLam := by
  have H (n:ℕ) : ∃Q : ActualHighOnlyOverlapMinimum (dim n+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0 1 Dchild T,
      Q.context=(a n).childData ∧ Q.R=(a n).Z ∧
        Q.xs=x n ∧ Q.lam=(a n).childLam :=
    (a n).exists_successful_minimum hc0 hc01 (hx n)
      hcl hcu hcl1 hcu1 hC (hd n) (hfull n) (hdD n)
      (hupper n) (hlower n) (htotal n) (hquantile n)
  choose Q0 hQ0 using H
  let Q := fun n=>(Q0 n).weakenConstants
    (le_refl (cl/4)) (le_refl (4*cu)) (le_refl (4*C/cl))
    hCt (le_refl Dchild) (le_refl T)
  refine ⟨Q,?_⟩
  intro n
  simpa only [Q,ActualHighOnlyOverlapMinimum.weakenConstants] using hQ0 n

end ActualHighOnlyChildBarrierCall
end OAI.SKFluctuations.LaplaceWindowFormalization
