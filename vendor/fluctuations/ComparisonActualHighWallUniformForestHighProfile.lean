module

public import ComparisonActualHighWallHighProfile
public import ComparisonActualHighWallGlobalHighEnvelopeAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem fixed_four_parent_weight_bound
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)| ≤
      Bclock/(Real.exp (-4*Bclock)*cK) := by
  have H:=M.data.four_G_weight_bound M.alpha ho hs hU hW hcK hstarK st tag
  have Hd : Real.exp (-4*Bclock)*cK ≤ Real.exp (-4*M.data.T)*cK:=
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith only [M.hT])) hcK.le
  exact H.trans ((div_le_div_of_nonneg_left M.data.hTpos.le
    (mul_pos (Real.exp_pos _) hcK) Hd).trans
    (div_le_div_of_nonneg_right M.hT (mul_pos (Real.exp_pos _) hcK).le))

theorem fixed_four_forest_high_profile_le_edges
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (ho : MassOrdered 0 as) (hist : i ≤ star) (hs : star<U) (hU : U≤as.length)
    {W cK : ℝ} (hW : 0<W) (hcK : 0<cK)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (seedMass : ℝ) (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    let rows:=actualGeneralFourCenteredForest (n:=n) M.bf M.hf hs hU W depth
      [nativeActualInitialState as i star seedMass (hist.trans (hs.le.trans hU))]
    (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth*edgeBudget 0 as f := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let root:=nativeActualInitialState (S:=Spin n×Bool) as i star seedMass (hist.trans (hs.le.trans hU))
  have hBc : 0 ≤ Bclock:=M.data.hTpos.le.trans M.hT
  have H:=nativeActualFourCenteredForest_wholeProfile_le ho (nativeOriginalHighRowGamma U K)
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    (fun Q tag=>nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag))
    (show 0 ≤ Bclock/(Real.exp (-4*Bclock)*cK) from div_nonneg hBc (mul_pos (Real.exp_pos _) hcK).le)
    (fun Q tag=>M.fixed_four_parent_weight_bound ho hs hU hW hcK hstarK Q tag) depth [root] 2
    (by intro Q hQ;have Hq : Q=root:=List.mem_singleton.mp hQ;subst Q;
        exact nativeActualInitialState_leaves_le as i star seedMass (hist.trans (hs.le.trans hU))) f hf hlo
  have Hfork:=nativeActualInitialState_high_forkCost_zero (S:=Spin n×Bool) as i star U hist hs
    (hist.trans (hs.le.trans hU)) seedMass f hlo
  have Hforkroot : root.tree.forkCost f=0:=Hfork
  have Hcoeff : root.term.coefficient=1:=rfl
  simpa only [actualGeneralFourCenteredForest,K,b,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Hcoeff,abs_one,one_mul,Hforkroot,zero_add] using H

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
