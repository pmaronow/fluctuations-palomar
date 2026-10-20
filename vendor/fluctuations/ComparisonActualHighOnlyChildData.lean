module

public import ComparisonActualHighOnlyChildBarrierCall

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ} (a : ActualHighOnlyComparisonData n delta)

def childData (alpha : a.Profile) {lam Echild dchild : ℝ}
    (hlam : lam∈Icc (0:ℝ) (a.d^2)) (hE : 0<Echild) (hd : 0<dchild)
    (hroom : lam+dchild^2 ≤ a.b a.s)
    (hcross : ∀u∈Ico (0:ℝ) a.s,a.b u+lam+dchild^2 ≤ a.b a.s) :
    ActualHighOnlyComparisonData n delta where
  E:=Echild
  d:=dchild
  s:=a.s
  b:=fun u=>a.b u-a.coefficient alpha lam u
  h:=fun u=>a.h u+a.coefficient alpha lam u*a.R alpha u
  hn:=a.hn
  hE:=hE
  hd:=hd
  hs:=a.hs
  hq:=a.hq
  hb:=(a.clocks_admissible alpha hlam).1
  hh:=(a.clocks_admissible alpha hlam).2.1
  hb0:=(a.clocks_admissible alpha hlam).2.2.1 0 ⟨le_rfl,zero_le_one⟩
  hh0:=(a.clocks_admissible alpha hlam).2.2.2 0 ⟨le_rfl,zero_le_one⟩
  hcut:=by
    have HR:a.R alpha a.s=0:=omittedSweepQuantile_left zero_le_one ⟨a.hs.1,a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM alpha
    have He:a.coefficient alpha lam a.s=lam:=by
      change omittedStrengthCoefficient a.d a.s (a.R alpha) lam a.s=lam
      rw [omittedStrengthCoefficient,ite_eq_left le_rfl,HR]
      simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]
    rw [He]
    linarith
  hcross:=by
    intro u hu
    have HE:a.coefficient alpha lam u=0:=by
      change omittedStrengthCoefficient a.d a.s (a.R alpha) lam u=0
      simp only [omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu.2)]
    have HR:a.R alpha a.s=0:=omittedSweepQuantile_left zero_le_one ⟨a.hs.1,a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM alpha
    have He:a.coefficient alpha lam a.s=lam:=by
      change omittedStrengthCoefficient a.d a.s (a.R alpha) lam a.s=lam
      rw [omittedStrengthCoefficient,ite_eq_left le_rfl,HR]
      simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]
    rw [HE,He]
    linarith [hcross u hu]

theorem exists_child_barrier_call {lam Echild dchild err : ℝ}
    (hlam : 0<lam) (hld : lam ≤ a.d^2)
    (M : ActualHighOnlyComparisonMinimum a lam) (hE : 0<Echild) (hd : 0<dchild)
    (hroom : lam+dchild^2 ≤ a.b a.s)
    (hcross : ∀u∈Ico (0:ℝ) a.s,a.b u+lam+dchild^2 ≤ a.b a.s)
    (hsuccess : (a.childData M.alpha ⟨hlam.le,hld⟩ hE hd hroom hcross).cost (dchild^2) ≤ err) :
    ∃call : ActualHighOnlyChildBarrierCall n delta,
      call.context=a ∧ call.lam=lam ∧ HEq call.optimizer M ∧
      call.childData=a.childData M.alpha ⟨hlam.le,hld⟩ hE hd hroom hcross ∧
      call.childLam=dchild^2 ∧ call.err=err := by
  let child:=a.childData M.alpha ⟨hlam.le,hld⟩ hE hd hroom hcross
  have Hlam:dchild^2∈Icc (0:ℝ) (child.d^2):=⟨(sq_pos_of_pos hd).le,le_rfl⟩
  obtain ⟨childMin⟩:=child.exists_actual_minimum Hlam
  have Hsuccess:child.objective (dchild^2) childMin.alpha ≤
      realOrderedSKPathPressure n child.b child.h 0+err:=by
    have Hcost:child.cost (dchild^2)=child.minimum (dchild^2)-realOrderedSKPathPressure n child.b child.h 0:=rfl
    rw [Hcost] at hsuccess
    rw [childMin.attained]
    linarith
  let call:ActualHighOnlyChildBarrierCall n delta:={
    context:=a
    lam:=lam
    hlam:=hlam
    hld:=hld
    optimizer:=M
    childData:=child
    childLam:=dchild^2
    hchildLam:=sq_pos_of_pos hd
    hchildLd:=le_rfl
    childOptimizer:=childMin
    sameInitialMass:=rfl
    childBareMatrix:=rfl
    childBareField:=rfl
    err:=err
    childSuccess:=Hsuccess}
  exact ⟨call,rfl,rfl,HEq.rfl,rfl,rfl,rfl⟩

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
