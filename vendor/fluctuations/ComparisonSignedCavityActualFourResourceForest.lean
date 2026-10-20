module

public import ComparisonSignedCavityActualMinimumFourResourceRecursion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

def nativeActualFourCenteredForest
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ) :
    ℕ→List (NativeActualResourceState S as i star)→List (NativeActualResourceState S as i star)
  | 0,xs=>xs.flatMap (fun Q=>[Q,Q.freeze])
  | depth+1,xs=>(nativeActualFourCenteredForest Γ hs hl weight depth xs).flatMap
      (nativeActualWeightedBranchStep Γ hs hl nativeActualOriginalFourGCenteredBranches weight)

theorem nativeActualFourCenteredForest_centered
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star)) :
    ∃ys : List (NativeActualResourceState S as i star),
      nativeActualFourCenteredForest Γ hs hl weight depth xs=ys.flatMap (fun Q=>[Q,Q.freeze]) := by
  cases depth with
  | zero=>exact ⟨xs,rfl⟩
  | succ depth=>
    refine ⟨(nativeActualFourCenteredForest Γ hs hl weight depth xs).flatMap
      (nativeActualWeightedBranchStep Γ hs hl nativeActualOriginalFourGBranches weight),?_⟩
    simp only [nativeActualFourCenteredForest,nativeActualOriginalFourGCenteredBranches,
      List.flatMap_assoc]
    apply congrArg (fun f=>(nativeActualFourCenteredForest Γ hs hl weight depth xs).flatMap f)
    funext Q
    exact nativeActualWeightedBranchStep_append_center Γ hs hl
      nativeActualOriginalFourGBranches weight Q

theorem nativeActualFourCenteredForest_valid
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star)) {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term) :
    ∀Q∈nativeActualFourCenteredForest Γ hs hl weight depth xs,
      NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
  induction depth with
  | zero=>
    intro Q hQ
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with rfl|rfl
    · exact hxs _ hP
    · exact (hxs _ hP).freeze
  | succ depth ih=>
    intro Q hQ
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    exact nativeActualWeightedBranchStep_valid Γ hs hl nativeActualOriginalFourGCenteredBranches
      weight P (ih P hP) Q hQ

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

def nativeActualOriginalFourRecursionError
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let children:=nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGBranches
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) st
  (W⁻¹)^st.generation/(chi*K star)*nativeActualOriginalFourResourceDefect M U st-
    (children.map (fun Q=>nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W Q.freeze)).sum

theorem actual_minimum_centered_four_resource_level
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W≠0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let F : NativeActualResourceState (Spin n×Bool) as i star→ℝ :=
    nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
    let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
    let zs:=xs.flatMap (fun Q=>[Q,Q.freeze])
    (zs.map F).sum=
      (zs.map (nativeActualOriginalFourRecursionError M hs hU W)).sum+
      ((zs.flatMap (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map F).sum := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let F : NativeActualResourceState (Spin n×Bool) as i star→ℝ :=
    nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let zs:=xs.flatMap (fun Q=>[Q,Q.freeze])
  let G : NativeActualResourceState (Spin n×Bool) as i star→ℝ :=
    nativeOriginalClockFourGStepResponse hs hU K b C 0 qfull 0 0 qfull 0 W
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let E:=fun Q : NativeActualResourceState (Spin n×Bool) as i star=>
    (W⁻¹)^Q.generation/(chi*K star)*nativeActualOriginalFourResourceDefect M U Q
  let H:=fun Q : NativeActualResourceState (Spin n×Bool) as i star=>
    ((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight Q).map
      (fun R=>F R.freeze)).sum
  have Hzvalid : ∀Q∈zs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
    intro Q hQ
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with rfl|rfl
    · exact hxs _ hP
    · exact (hxs _ hP).freeze
  have Hsource : (zs.map (fun Q=>F Q+F Q.freeze)).sum=
      (zs.map (fun Q=>E Q+G Q+G Q.freeze)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro Q hQ
    exact actual_minimum_centered_resource_four_recursion M Q (Hzvalid Q hQ) hi hs ho W hW hstarK
  have HFzero:=nativeOriginalClock_centered_list_frozen_sum ho U K b C 0 qfull 0 0 qfull 0 W xs
  have HGzero:=nativeOriginalClockFourGStepResponse_centered_list_frozen_sum ho hs hU K b C
    0 qfull 0 0 qfull 0 W hW xs
  change (zs.map (fun Q=>F Q.freeze)).sum=0 at HFzero
  change (zs.map (fun Q=>G Q.freeze)).sum=0 at HGzero
  simp only [List.sum_map_add,HFzero,HGzero,add_zero] at Hsource
  have Hnext :
      ((zs.flatMap (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight)).map F).sum=
      (zs.map G).sum+(zs.map H).sum := by
    simp only [List.map_flatMap,native_sum_flatMap]
    have HQ (Q : NativeActualResourceState (Spin n×Bool) as i star) :
        ((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGCenteredBranches weight Q).map F).sum=G Q+H Q :=
      nativeOriginalClockFourGBranches_centered_response hs hU Q K b C 0 qfull 0 0 qfull 0 W
    simp_rw [HQ]
    exact List.sum_map_add
  change (zs.map F).sum=(zs.map (fun Q=>E Q-H Q)).sum+
    ((zs.flatMap (nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
      nativeActualOriginalFourGCenteredBranches weight)).map F).sum
  rw [sum_map_sub_explicit,Hnext]
  linarith only [Hsource]

end OAI.SKFluctuations.Cavity
