module

public import ComparisonActualGeneralTargetMeanReadout
public import ComparisonSignedCavityActualConstantStarFourCalibration

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {as : List PositiveMass} {star U : ℕ}
theorem actual_general_constant_star_response_eq_original
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (W : ℝ) (star U : ℕ) (hstar : star≤as.length) :
    let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection hstar
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 (singleSlot as) star
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let S:=nativePhysicalResourceCenter n bf hf as
    let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
    actualGeneralFourStateResponse bf hf U W st=
      W⁻¹*nativeOriginalLongitudinalPairing n 0 q 0 U K b S g.tree
        (fun σ=>deletedOverlap n (joinSpin (T.atSlot (g.restrict σ) (singleSlot as)))
          (joinSpin (g.spin σ))-S star) (g.embed (singleSlot as)) := by
  dsimp only
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let S:=nativePhysicalResourceCenter n bf hf as
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  have Hzero (σ : base.tree.Assignment) : base.term.value (fullWeight n) (fullFeature n)
      0 q (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) S 0 σ=1:=by
    simp [base,nativeActualConstantState,NativeResourceTerm.value,NativeResourceTerm.scalar,
      NativeResourceTerm.ofLive,nativeResourceConstant,NativeGeneratedTest.value,
      nativeGeneratedEdgeProduct,NativeGeneratedTest.edges]
  have H:=nativeOriginalClockResourceResponse_projection base.term U 0 K b S 0 q 0 0 q 0 W hstar
  dsimp only at H
  simp_rw [Hzero,one_mul] at H
  simpa only [actualGeneralFourStateResponse,nativeOriginalClockStateResponse,
    NativeActualResourceState.projection,nativeActualConstantState,base,pow_one,
    nativeResourceConstant,NativeResourceTerm.ofLive,Nat.zero_add] using H

theorem actual_general_constant_star_frozen_response_eq_exact_physical_mean
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (star U : ℕ) (hstar : star≤as.length) :
    let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection hstar
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let S:=nativePhysicalResourceCenter n bf hf as
    let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
    actualGeneralFourStateResponse bf hf U W st.freeze=
      -W⁻¹*(finitePhysicalMean (n+1) as b h star-
        finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)*
      nativeOriginalLongitudinalPairing n 0 q 0 U K b S st.tree (fun _=>1) st.term.live.test.target := by
  dsimp only
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  let st:=base.projection hstar
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let S:=nativePhysicalResourceCenter n bf hf as
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
  simpa only [actualGeneralFourStateResponse,nativeOriginalClockStateResponse,
    NativeActualResourceState.freeze,st,base,NativeActualResourceState.projection,
    nativeActualConstantState,Nat.zero_add,pow_one] using HF

end OAI.SKFluctuations.Cavity
