module

public import ComparisonActualHighWallFreshPairOnGrid
public import ComparisonActualHighWallUniformForestHighProfile
public import ComparisonActualGeneralConstantJointFourReadout
public import ComparisonActualGeneralFourCollectiveIteration
public import ComparisonSignedCavityActualFourForestTaylorVariation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_four_forest_coefficient_variation_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length)
    {W cK : ℝ} (hW : 0<W) (hcK : 0<cK)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (depth r : ℕ) (roots : List (NativeActualResourceState (Spin n×Bool) as i star))
    (hr : ∀Q∈roots,Q.tree.leaves≤r) :
    ((actualGeneralFourCenteredForest M.bf M.hf hs hU W depth roots).map
      (fun Q=>|Q.term.coefficient|)).sum ≤
      2*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 r depth*
        (roots.map (fun Q=>|Q.term.coefficient|)).sum := by
  have hBc : 0≤Bclock:=M.data.hTpos.le.trans M.hT
  exact nativeActualFourCenteredForest_coefficient_variation_le ho
    (nativeOriginalHighRowGamma U (nativeContinuumMixedClock n M.bf M.hf as))
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U _ Q p)
    hs (hs.le.trans hU) _ (div_nonneg hBc (mul_pos (Real.exp_pos _) hcK).le)
    (fun Q tag=>M.fixed_four_parent_weight_bound ho hs hU hW hcK hstarK Q tag)
    depth roots r hr

theorem actual_high_wall_four_fresh_pair_forest_abs_le_on_grid
    {n degree : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass cK : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallSquareResourcePairBudgetsOnGrid degree A saving Cmass M u as)
    (hd : 1≤degree) (hA : 1≤A) (ho : MassOrdered 0 as)
    {i U : ℕ} {seed : List NativeResourceMark}
    (hseed : seed=[] ∨ seed=[.initial]) (hs : retainedMassPrefixIndex u.val as<U)
    (hU : U≤as.length) (hcK : 0<cK)
    (hstarK : cK*M.data.d≤nativeContinuumMixedClock n M.bf M.hf as
      (retainedMassPrefixIndex u.val as))
    (depth r k : ℕ)
    (roots : List (NativeActualResourceState (Spin n×Bool) as i (retainedMassPrefixIndex u.val as)))
    (hroots : ∀Q∈roots,NativeActualResourceGenerated i (retainedMassPrefixIndex u.val as)
      U seed Q.generation Q.tree Q.term)
    (hk : ∀Q∈roots,Q.generation=k) (hr : ∀Q∈roots,Q.tree.leaves≤r)
    (hdegree : seed.length+k+depth≤degree)
    (hi : i≤retainedMassPrefixIndex u.val as)
    (hmass : partitionPoint 0 as i≤Cmass*M.data.d) :
    let epsilon:=((n+1:ℕ):ℝ)^(-saving)
    |actualGeneralFourPairSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth roots)| ≤
      (2*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 r depth*
        (roots.map (fun Q=>|Q.term.coefficient|)).sum)*
      (3*A^(seed.length+(k+depth)+1)*nativeResourceScale M.data.d M.data.d epsilon seed*
        epsilon^(k+depth+1)*M.data.d) := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i
      (retainedMassPrefixIndex u.val as)) tag=>nativeOriginalClockParentWeight M.data.d U K Q
    (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let rows:=actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth roots
  let epsilon:=((n+1:ℕ):ℝ)^(-saving)
  let B:=3*A^(seed.length+(k+depth)+1)*nativeResourceScale M.data.d M.data.d epsilon seed*
    epsilon^(k+depth+1)*M.data.d
  have hB : 0≤B:=by
    have hdpos : 0<M.data.d:=M.data.hd
    have Hscale : 0≤nativeResourceScale M.data.d M.data.d epsilon seed:=by
      rcases hseed with hzero|hone
      · rw [hzero];norm_num [nativeResourceScale]
      · rw [hone];simpa only [nativeResourceScale,List.map_singleton,List.prod_singleton,
          NativeResourceMark.savedScale] using hdpos.le
    dsimp only [B];positivity
  have HQ (Q) (hQ : Q∈rows) :
      |(M.data.d⁻¹)^Q.generation*actualGeneralFourPairContrast M.bf M.hf U Q| ≤
        |Q.term.coefficient| *B:=by
    have HV:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight
      depth roots hroots Q hQ
    have HG:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight
      depth roots k hk Q hQ
    have HB:=actual_high_wall_four_fresh_pair_abs_le_on_grid H hd hA ho hseed Q HV
      (by omega) hi hs hU hmass
    rw [HG] at HB ⊢
    simpa only [B,epsilon,mul_assoc,mul_left_comm,mul_comm] using HB
  have HC:=actual_high_wall_four_forest_coefficient_variation_le M ho hs hU M.data.hd
    hcK hstarK depth r roots hr
  change |(rows.map (fun Q=>(M.data.d⁻¹)^Q.generation*
    actualGeneralFourPairContrast M.bf M.hf U Q)).sum|≤_
  apply (native_abs_sum_map_le _ _).trans
  apply (List.sum_le_sum HQ).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right HC hB

end OAI.SKFluctuations.Cavity
