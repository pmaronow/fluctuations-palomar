module

public import ComparisonSignedCavityActualOriginalGBranchSource
public import ComparisonSignedCavityActualResourceFrontierWords

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 10000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem NativeActualResourceState.freeze_reweight
    (st : NativeActualResourceState S as i star) (c : ℝ) :
    (st.reweight c).freeze=st.freeze.reweight c := by
  simp [NativeActualResourceState.freeze,NativeActualResourceState.reweight,
    NativeResourceTerm.freeze,NativeResourceTerm.reweight,mul_neg]

theorem nativeActualWeightedBranchStep_append_center
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (st : NativeActualResourceState S as i star) :
    nativeActualWeightedBranchStep Γ hs hl
      (branches.map (fun b=>(b.1,b.2++[.center]))) weight st=
    (nativeActualWeightedBranchStep Γ hs hl branches weight st).flatMap (fun Q=>[Q,Q.freeze]) := by
  unfold nativeActualWeightedBranchStep
  rw [List.flatMap_map,List.flatMap_assoc]
  apply congrArg (fun f=>branches.flatMap f)
  funext b
  dsimp only
  rw [nativeActualResourceExpansion_append,List.map_flatMap,List.flatMap_map]
  apply congrArg (fun f=>(nativeActualResourceExpansion Γ hs hl b.2 st).flatMap f)
  funext Q
  simp [nativeActualResourceExpansion,nativeActualResourceStep,
    NativeActualResourceState.freeze_reweight]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal

def nativeActualOriginalGCenteredBranches : NativeActualWeightedBranches :=
  nativeActualOriginalGBranches.map (fun b=>(b.1,b.2++[.center]))

theorem nativeActualOriginalGCenteredBranches_eq :
    nativeActualOriginalGCenteredBranches=[(0,[.projection,.center]),(1,[.highRow,.center])] := rfl

theorem nativeActualOriginalGCenteredBranches_response
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (hs : star < U) (hl : star ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    let K:=retainedStarMixedClock n M.bf M.hf as
    let Γ:=nativeOriginalHighRowGamma (n:=n) U K
    let weight:=fun parent tag=>nativeActualParentRecursionWeight M W U parent
      (nativeActualOriginalGBranchBeta M U parent tag)
    let children:=nativeActualWeightedBranchStep Γ hs hl nativeActualOriginalGBranches weight st
    let F:=nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W
    ((nativeActualWeightedBranchStep Γ hs hl nativeActualOriginalGCenteredBranches weight st).map F).sum=
      (children.map F).sum+(children.map (fun Q=>F Q.freeze)).sum := by
  dsimp only
  rw [nativeActualOriginalGCenteredBranches,nativeActualWeightedBranchStep_append_center]
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero]
  exact List.sum_map_add

end OAI.SKFluctuations.Cavity
