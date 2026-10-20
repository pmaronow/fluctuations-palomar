module

public import ComparisonSignedCavityActualFourResourceForest

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualMinimumFourCenteredForest
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    List (NativeActualResourceState (Spin n×Bool) as i star) :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  nativeActualFourCenteredForest (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) depth xs

def nativeActualMinimumFourStateResponse
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (W : ℝ) (Q : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W Q

def nativeActualMinimumFourResidualSum
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun j=>
    ((nativeActualMinimumFourCenteredForest M hs hU W j xs).map
      (nativeActualOriginalFourRecursionError M hs hU W)).sum)).sum

theorem actual_minimum_four_resource_forest_level
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W ≠ 0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    ((nativeActualMinimumFourCenteredForest M hs hU W depth xs).map
      (nativeActualMinimumFourStateResponse M U W)).sum=
    ((nativeActualMinimumFourCenteredForest M hs hU W depth xs).map
      (nativeActualOriginalFourRecursionError M hs hU W)).sum+
    ((nativeActualMinimumFourCenteredForest M hs hU W (depth+1) xs).map
      (nativeActualMinimumFourStateResponse M U W)).sum := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  obtain ⟨ys,hys⟩:=nativeActualFourCenteredForest_centered Γ hs (hs.le.trans hU) weight depth xs
  have Hv:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth xs hxs
  have Hy : ∀Q∈ys,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
    intro Q hQ
    apply Hv Q
    rw [hys]
    exact List.mem_flatMap.mpr ⟨Q,hQ,by simp⟩
  have H:=actual_minimum_centered_four_resource_level M ys Hy hi hs hU ho W hW hstarK
  change ((ys.flatMap (fun Q=>[Q,Q.freeze])).map
      (nativeActualMinimumFourStateResponse M U W)).sum=
    ((ys.flatMap (fun Q=>[Q,Q.freeze])).map
      (nativeActualOriginalFourRecursionError M hs hU W)).sum+
    (((ys.flatMap (fun Q=>[Q,Q.freeze])).flatMap
      (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map
      (nativeActualMinimumFourStateResponse M U W)).sum at H
  rw [←hys] at H
  exact H

theorem actual_minimum_four_resource_finite_iteration
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W ≠ 0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    ((xs.flatMap (fun Q=>[Q,Q.freeze])).map
      (nativeActualMinimumFourStateResponse M U W)).sum=
    nativeActualMinimumFourResidualSum M hs hU W depth xs+
    ((nativeActualMinimumFourCenteredForest M hs hU W depth xs).map
      (nativeActualMinimumFourStateResponse M U W)).sum := by
  induction depth with
  | zero=>simp [nativeActualMinimumFourResidualSum,nativeActualMinimumFourCenteredForest,
      nativeActualFourCenteredForest]
  | succ depth ih=>
    have H:=actual_minimum_four_resource_forest_level M xs hxs hi hs hU ho W hW hstarK depth
    rw [H] at ih
    simpa only [nativeActualMinimumFourResidualSum,List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton,add_assoc] using ih

end OAI.SKFluctuations.Cavity
