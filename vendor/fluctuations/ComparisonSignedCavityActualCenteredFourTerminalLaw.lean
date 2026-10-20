module

public import ComparisonSignedCavityActualFourResourceIteration
public import ComparisonSignedCavityActualFourGContinuumTerminalFromPairs

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualFourCenteredForest_eq_seed_frontiers
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star<U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star)) :
    nativeActualFourCenteredForest Γ hs hl weight depth xs=
      (xs.flatMap (fun Q=>[Q,Q.freeze])).flatMap
        (nativeActualWeightedFrontier Γ hs hl nativeActualOriginalFourGCenteredBranches
          weight depth) := by
  induction depth with
  | zero=>simp [nativeActualFourCenteredForest,nativeActualWeightedFrontier]
  | succ depth ih=>
    rw [nativeActualFourCenteredForest,ih]
    simp only [List.flatMap_assoc,nativeActualWeightedFrontier]

theorem nativeActualFourCenteredForest_singleton
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star<U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (st : NativeActualResourceState S as i star) :
    nativeActualFourCenteredForest Γ hs hl weight depth [st]=
      nativeActualWeightedFrontier Γ hs hl nativeActualOriginalFourGCenteredBranches
        weight depth st ++
      nativeActualWeightedFrontier Γ hs hl nativeActualOriginalFourGCenteredBranches
        weight depth st.freeze := by
  rw [nativeActualFourCenteredForest_eq_seed_frontiers]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem nativeActualFourCenteredForest_singleton_response
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star<U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (st : NativeActualResourceState S as i star)
    (F : NativeActualResourceState S as i star→ℝ) :
    ((nativeActualFourCenteredForest Γ hs hl weight depth [st]).map F).sum=
      ((nativeActualWeightedFrontier Γ hs hl nativeActualOriginalFourGCenteredBranches
        weight depth st).map F).sum+
      ((nativeActualWeightedFrontier Γ hs hl nativeActualOriginalFourGCenteredBranches
        weight depth st.freeze).map F).sum := by
  rw [nativeActualFourCenteredForest_singleton,List.map_append,List.sum_append]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def nativeActualOriginalContinuumFrozenSeedFourGFrontier
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (depth : ℕ) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
    (nativeOriginalClockFourGBranchBeta U K b parent tag)
  ((nativeActualWeightedFrontier (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGCenteredBranches weight depth
    (nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))).freeze).map
    (nativeOriginalClockStateResponse U K b C 0 q 0 0 q 0 W)).sum

def nativeActualOriginalContinuumCenteredFourGFrontier
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (depth : ℕ) : ℝ :=
  ((nativeActualMinimumFourCenteredForest M hs hU W depth
    [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]).map
    (nativeActualMinimumFourStateResponse M U W)).sum

theorem native_actual_original_centered_four_G_frontier_eq_two_seeds
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (depth : ℕ) :
    nativeActualOriginalContinuumCenteredFourGFrontier M as W i star U hi hs hU depth=
      nativeActualOriginalContinuumFourGFrontier M as W i star U hi hs hU depth+
      nativeActualOriginalContinuumFrozenSeedFourGFrontier M as W i star U hi hs hU depth := by
  unfold nativeActualOriginalContinuumCenteredFourGFrontier
    nativeActualMinimumFourCenteredForest nativeActualMinimumFourStateResponse
    nativeActualOriginalContinuumFourGFrontier nativeActualOriginalContinuumFrozenSeedFourGFrontier
  exact nativeActualFourCenteredForest_singleton_response _ _ _ _ _ _ _

theorem actual_minimum_initial_four_resource_finite_iteration
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    nativeActualMinimumFourStateResponse M U W st+
      nativeActualMinimumFourStateResponse M U W st.freeze=
      nativeActualMinimumFourResidualSum M hs hU W depth [st]+
      nativeActualOriginalContinuumCenteredFourGFrontier M as W i star U hi hs hU depth := by
  dsimp only
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have Hv : ∀Q∈[st],NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term:=by
    intro Q hQ
    obtain rfl:=List.mem_singleton.mp hQ
    exact hst
  have H:=actual_minimum_four_resource_finite_iteration M [st] Hv hi hs hU ho W hW hstarK depth
  simpa only [nativeActualOriginalContinuumCenteredFourGFrontier,st,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero] using H

end OAI.SKFluctuations.Cavity
