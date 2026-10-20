module

public import ComparisonNativeActualChildSweep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

namespace NativeChildBarrierParameters

theorem profile_nonempty {n : ℕ} {delta : ℝ} (c : NativeChildBarrierParameters n delta)
    (hq : 2 ≤ c.N^delta) : c.Profile.Nonempty := by
  have hMc : Continuous c.M := comparisonCap_continuous _ _ _ _ _ _
  have hne : (inverseDifferentialConstraints 0 0 c.k c.M).Nonempty :=
    comparisonConstraints_nonempty c.hN c.hU c.hL (min_le_left _ _) c.hE c.hd.le hq
      (by norm_num) (by norm_num)
  rw [inverseDifferentialConstraints_eq 0 0 zero_le_one c.k c.M c.hk hMc c.hm c.hM] at hne
  exact hne

def actualChild {n : ℕ} {delta lam c0 x : ℝ}
    (c : NativeChildBarrierParameters n delta)
    (hlam : 0 < lam) (hc0 : 0 < c0) (hx : 0 < x) :
    NativeChildBarrierParameters n delta where
  E:=actualChildErrorBudget n delta c0 c.d lam x
  d:=actualChildRadius c0 x
  hn:=c.hn
  hE:=actual_child_budget_pos c.hN hc0 hlam hx
  hd:=mul_pos hc0 hx

end NativeChildBarrierParameters

theorem native_actual_child_call_exists {n : ℕ} {delta lam childLam : ℝ}
    (c child : NativeChildBarrierParameters n delta)
    (α : c.Profile) (b h : ℝ → ℝ)
    (hlam : 0 < lam) (hchildLam : 0 < childLam)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (hroom : lam+childLam ≤ b 0)
    (hminimum : ∀β : c.Profile,
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam α ≤
      comparisonVariableEndpointObjective c.hc c.hk c.hkc c.hm c.hM n b h c.d lam β)
    (hq : 2 ≤ child.N^delta) :
    let bc:=fun u=>b u-laplaceComparisonStrength c.d lam (c.R α u)
    let hc:=fun u=>h u+laplaceComparisonStrength c.d lam (c.R α u)*c.R α u
    ∃β : child.Profile,∃a : NativeChildBarrierCall n delta,
      a.context=c ∧ a.lam=lam ∧ HEq a.alpha α ∧ a.b=b ∧ a.h=h ∧
      a.childRadius=child.d ∧ a.childLam=childLam ∧ a.Z=child.R β ∧
      a.err=variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
        n bc hc child.d childLam ∧ a.err∈Icc (0:ℝ) childLam ∧
      variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
        n bc hc child.d childLam β=
      variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
        n bc hc child.d childLam := by
  dsimp only
  let bc:=fun u=>b u-laplaceComparisonStrength c.d lam (c.R α u)
  let hc:=fun u=>h u+laplaceComparisonStrength c.d lam (c.R α u)*c.R α u
  have hparent:=comparisonVariableEndpoint_clocks_admissible c.hc c.hk c.hkc c.hm c.hM
    b h c.hd.ne' hlam.le (by linarith) hb hh hh0 α
  have hbc : MonotoneOn bc (Icc (0:ℝ) 1) := hparent.1
  have hhc : MonotoneOn hc (Icc (0:ℝ) 1) := hparent.2.1
  have hhc0 : 0 ≤ hc 0 := hparent.2.2.2
  have hroom' : childLam ≤ bc 0 := by
    have he:=laplaceComparisonStrength_le c.d hlam.le (c.R α 0)
    dsimp only [bc]
    linarith
  have hMc : Continuous child.M := comparisonCap_continuous _ _ _ _ _ _
  have hne:=child.profile_nonempty hq
  obtain ⟨β,hβ,_⟩:=variableEndpointComparisonSweepMinimum_attained
    child.hc child.hk child.hkc child.hm child.hM n c.hn bc hc child.hd.ne'
    hchildLam.le hroom' hbc hhc hhc0 hMc hne
  let err:=variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
    n bc hc child.d childLam
  have herr0 : 0 ≤ err := variableEndpointComparisonSweepCost_nonneg child.hc child.hk
    child.hkc child.hm child.hM n c.hn bc hc child.hd.ne' hroom' hbc hhc hhc0
      hMc hne ⟨hchildLam.le,le_rfl⟩
  have herrL : err ≤ childLam := by
    have hv:=variableEndpointComparisonSweepCost_lipschitz child.hc child.hk child.hkc
      child.hm child.hM n c.hn bc hc child.hd.ne' hroom' hbc hhc hhc0 hMc hne
    have hz:=variableEndpointComparisonSweepCost_zero child.hc child.hk child.hkc
      child.hm child.hM n c.hn bc hc child.hd.ne' (hchildLam.le.trans hroom')
        hbc hhc hhc0 hMc hne
    have hh:=hv.dist_le_mul childLam ⟨hchildLam.le,le_rfl⟩ 0 ⟨le_rfl,hchildLam.le⟩
    rw [hz,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,abs_of_pos hchildLam,NNReal.coe_one,one_mul] at hh
    exact (le_abs_self _).trans hh
  have hsuccess : pathCompensatedPressure n bc hc
      (fun u=>laplaceComparisonStrength child.d childLam (child.R β u)) (child.R β) 0 ≤
        realOrderedSKPathPressure n bc hc 0+err := by
    change variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
      n bc hc child.d childLam β ≤ _
    rw [hβ]
    dsimp only [err,variableEndpointComparisonSweepCost]
    linarith
  let a : NativeChildBarrierCall n delta :=
    { context:=c,lam:=lam,childRadius:=child.d,childLam:=childLam,
      hlam:=hlam,hchildRadius:=child.hd.ne',hchildLam:=hchildLam,
      alpha:=α,b:=b,h:=h,Z:=child.R β,hb:=hb,hh:=hh,hh0:=hh0,matrixRoom:=hroom,
      hZc:=(comparisonSweepQuantile_continuous child.hc child.hk child.hkc child.hm child.hM β).continuousOn,
      hZm:=(comparisonSweepQuantile_monotone child.hc child.hk child.hkc child.hm child.hM β).monotoneOn _,
      hZb:=fun u _=>comparisonSweepQuantile_bounds child.hc child.hk child.hkc child.hm child.hM β u,
      minimum:=hminimum,err:=err,childSuccess:=hsuccess }
  exact ⟨β,a,rfl,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨herr0,herrL⟩,hβ⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
