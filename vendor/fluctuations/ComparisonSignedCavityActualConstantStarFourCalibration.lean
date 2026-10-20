module

public import ComparisonSignedCavityActualConstantStarFourTerminalFromPairs
public import ComparisonSignedCavityActualConstantForwardMean

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_minimum_constant_star_four_resource_finite_iteration
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (star U : ℕ)
    (hs : star < U) (hU : U≤as.length) (ho : MassOrdered 0 as)
    (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection (hs.le.trans hU)
    nativeActualMinimumFourStateResponse M U W st+
      nativeActualMinimumFourStateResponse M U W st.freeze=
      nativeActualMinimumFourResidualSum M hs hU W depth [st]+
      (nativeActualOriginalConstantStarFourGFrontier M as W star U hs hU depth false+
       nativeActualOriginalConstantStarFourGFrontier M as W star U hs hU depth true) := by
  dsimp only
  let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection (hs.le.trans hU)
  have hst : NativeActualResourceGenerated 0 star U [] st.generation st.tree st.term:=
    (show NativeActualResourceGenerated 0 star U []
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).generation
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).tree
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).term from
        .physical (.constant as hU)).projection (hs.le.trans hU)
  have H:=actual_minimum_four_resource_finite_iteration M [st]
    (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hst)
    (Nat.zero_le star) hs hU ho W hW hstarK depth
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,add_zero] at H
  unfold nativeActualMinimumFourCenteredForest at H
  rw [nativeActualFourCenteredForest_singleton_response] at H
  convert H using 1
  rfl

theorem actual_minimum_constant_star_response_eq_original
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (star U : ℕ) (hstar : star≤as.length) :
    let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection hstar
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 (singleSlot as) star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let S:=nativePhysicalResourceCenter n M.bf M.hf as
    let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualMinimumFourStateResponse M U W st=
      W⁻¹*nativeOriginalLongitudinalPairing n 0 q 0 U K b S g.tree
        (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) (singleSlot as)))
          (joinSpin (g.spin σ))-S star) (g.embed (singleSlot as)) := by
  dsimp only
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  have Hzero (σ : base.tree.Assignment) : base.term.value (fullWeight n) (fullFeature n)
      0 q (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0 σ=1:=by
    simp [base,nativeActualConstantState,NativeResourceTerm.value,NativeResourceTerm.scalar,
      NativeResourceTerm.ofLive,nativeResourceConstant,NativeGeneratedTest.value,
      nativeGeneratedEdgeProduct,NativeGeneratedTest.edges]
  have H:=nativeOriginalClockResourceResponse_projection base.term U 0 K b S 0 q 0 0 q 0 W hstar
  dsimp only at H
  simp_rw [Hzero,one_mul] at H
  simpa only [nativeActualMinimumFourStateResponse,nativeOriginalClockStateResponse,
    NativeActualResourceState.projection,nativeActualConstantState,base,pow_one,
    nativeResourceConstant,NativeResourceTerm.ofLive,Nat.zero_add] using H

theorem actual_minimum_constant_star_frozen_response_eq_exact_physical_mean
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (star U : ℕ) (hstar : star≤as.length) :
    let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection hstar
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let S:=nativePhysicalResourceCenter n M.bf M.hf as
    let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualMinimumFourStateResponse M U W st.freeze=
      -W⁻¹*(finitePhysicalMean (n+1) as b h star-
        finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)*
      nativeOriginalLongitudinalPairing n 0 q 0 U K b S st.tree (fun _=>1) st.term.live.test.target := by
  dsimp only
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  let st:=base.projection hstar
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let g:=nativeFreshAtSlot base.tree 0 base.term.live.test.target star
  have Hzero (σ : base.tree.Assignment) : base.term.value (fullWeight n) (fullFeature n)
      0 q (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0 σ=1:=by
    simp [base,nativeActualConstantState,NativeResourceTerm.value,NativeResourceTerm.scalar,
      NativeResourceTerm.ofLive,nativeResourceConstant,NativeGeneratedTest.value,
      nativeGeneratedEdgeProduct,NativeGeneratedTest.edges]
  have HV : st.term.value (fullWeight n) (fullFeature n) 0 q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0=
      fun σ=>deletedOverlap n (joinSpin (base.tree.atSlot (g.restrict σ) base.term.live.test.target))
        (joinSpin (g.spin σ))-S star:=by
    funext σ
    have H:=base.term.projection_value 0 0 hstar (fullWeight n) (fullFeature n) 0 q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0 σ
    dsimp only at H
    rw [Hzero,one_mul] at H
    simpa only [st,NativeActualResourceState.projection,base,nativeActualConstantState,g] using H
  have hsplit : g.tree.splitIndex (g.embed base.term.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,base.tree.splitIndex_self,Nat.min_eq_left hstar]
  have HM:=fullEndpoint_deleted_centered_mean_eq_exact_physical n U b h K g.tree ho
    (g.embed base.term.live.test.target) g.mark
    (nativeFreshAtSlot_distinct base.tree 0 base.term.live.test.target star base.term.live.test.target).symm (S star)
  have Hq : q=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K:=
    native_full_endpoint_clock_mixed_independent n _ U 1 b h _ K
  rw [hsplit,←Hq] at HM
  have HM' : st.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (st.term.value (fullWeight n) (fullFeature n) 0 q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0) 0=
      finitePhysicalMean (n+1) as b h star-finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star:=by
    rw [HV]
    change g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>deletedOverlap n (joinSpin (base.tree.atSlot (g.restrict σ) base.term.live.test.target))
        (joinSpin (g.spin σ))-S star) 0= _
    simp_rw [MarkedPlacement.restrict_at,MarkedPlacement.spin_at]
    exact HM
  have HF:=nativeOriginalClockResourceResponse_freeze st.term ho U st.generation K b S 0 q 0 0 q 0 W
  dsimp only at HF
  rw [HM'] at HF
  simpa only [nativeActualMinimumFourStateResponse,nativeOriginalClockStateResponse,
    NativeActualResourceState.freeze,st,base,NativeActualResourceState.projection,
    nativeActualConstantState,Nat.zero_add,pow_one] using HF

end OAI.SKFluctuations.Cavity
