module

public import ComparisonSignedCavityActualTargetGResponse
public import ComparisonSignedCavityActualTargetCutConditionalMean

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped NNReal
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem native_actual_target_response_original_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let T:=single (S:=Spin n×Bool) as
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    nativeActualTargetLongitudinalResponse M as i U=
      nativeOriginalLongitudinalPairing n 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 U K b C g.tree
        (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
          (joinSpin (g.spin σ))-C i) (g.embed s) := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  have HS : S=nativePhysicalResourceCenter n M.bf M.hf as:=by
    funext j
    exact native_ordered_source_center_eq_completed n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone (partitionPoint_mem as ho j)
  have HQ : cutFullVariance n q U 1 1 b h K=
      finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  change nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S
    g.tree (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) s))
      (joinSpin (g.spin σ))-S i) (g.embed s)=_
  rw [HQ,HS]

theorem native_actual_target_conditional_original_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i U : ℕ)
    (hi : i<U) (hU : U≤as.length) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    nativeActualTargetConditionalResponse M as i U=
      nativeOriginalConditionalLongitudinalPair (single (S:=Spin n×Bool) as) (singleSlot as)
        i U K b C 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i) := by
  dsimp only
  rw [←native_actual_target_longitudinal_eq_conditional M as ho i U hi hU,
    native_actual_target_response_original_readout M as ho i U]
  exact native_original_longitudinal_pair_eq_conditional_insertion
    (single (S:=Spin n×Bool) as) ho (singleSlot as) i U hi hU
    (nativeContinuumMixedClock n M.bf M.hf as)
    (fun j=>(M.bf (partitionPoint 0 as j):ℝ))
    (nativePhysicalResourceCenter n M.bf M.hf as) 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ)) 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)-nativePhysicalResourceCenter n M.bf M.hf as i)

end OAI.SKFluctuations.Cavity
