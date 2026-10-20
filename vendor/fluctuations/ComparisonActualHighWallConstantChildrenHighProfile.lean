module

public import ComparisonActualHighWallUniformForestHighProfile
public import ComparisonActualGeneralConstantJointFourReadout
public import ComparisonSignedCavityActualConstantChildHighProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem fixed_constant_children_high_profile_le_edges
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as star U hs hU).map
      (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      (1+nativeActualProfileOpVariation 1 .highRow)*edgeBudget 0 as f := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:=actual_general_continuum_chi_mem_unit_on_any_grid (n:=n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho U (by omega) hU
  have hchi : |chi|≤1:=by
    rw [abs_of_nonneg Hchi.1]
    exact Hchi.2
  have H:=native_actual_constant_child_family_wholeProfile_le (S:=Spin n×Bool) (i:=0) ho (nativeOriginalHighRowGamma (n:=n) U K)
    (fun st p _=>nativeOriginalHighRowGamma_abs_le_one (n:=n) ho U K st p) hs hU chi hchi f hf hlo
  simpa only [actualGeneralConstantSourceChildren,K,chi] using H

theorem fixed_constant_children_four_forest_high_profile_le_edges
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length) {W cK : ℝ} (hW : 0<W) (hcK : 0<cK)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    let rows:=actualGeneralFourCenteredForest (n:=n) M.bf M.hf hs hU W depth
      (actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as star U hs hU)
    (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      (2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 3 depth)*
        ((1+nativeActualProfileOpVariation 1 .highRow)*edgeBudget 0 as f) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let children:=actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as star U hs hU
  have hBc : 0≤Bclock:=M.data.hTpos.le.trans M.hT
  have hCost : 0≤2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
      (Bclock/(Real.exp (-4*Bclock)*cK)) 3 3 depth:=mul_nonneg (by norm_num)
    (nativeActualWeightedProfileFrontierCost_nonneg _ (by positivity) _ _ _)
  have H:=nativeActualFourCenteredForest_wholeProfile_le ho (nativeOriginalHighRowGamma (n:=n) U K)
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one (n:=n) ho U K Q p) hs (hs.le.trans hU)
    (fun Q tag=>nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag))
    (show 0≤Bclock/(Real.exp (-4*Bclock)*cK) from div_nonneg hBc (mul_pos (Real.exp_pos _) hcK).le)
    (fun Q tag=>M.fixed_four_parent_weight_bound ho hs hU hW hcK hstarK Q tag) depth children 3
    (fun Q hQ=>actualGeneralConstantSourceChildren_leaves M.bf M.hf hs hU Q hQ) f hf hlo
  have Hinit:=M.fixed_constant_children_high_profile_le_edges ho hs hU f hf hlo
  apply H.trans
  exact mul_le_mul_of_nonneg_left Hinit hCost

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
