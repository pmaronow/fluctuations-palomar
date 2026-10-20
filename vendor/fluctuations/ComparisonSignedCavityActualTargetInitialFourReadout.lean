module

public import ComparisonSignedCavityActualTargetGOriginalReadout
public import ComparisonSignedCavityActualCenteredFourTerminalLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_target_response_eq_initial_four_state
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i star U : ℕ) (hi : i≤as.length) (W : ℝ) :
    nativeActualTargetLongitudinalResponse M as i U=
      nativeActualMinimumFourStateResponse M U W (nativeActualInitialState as i star 0 hi) := by
  rw [native_actual_target_response_original_readout M as ho i U]
  unfold nativeActualMinimumFourStateResponse nativeOriginalClockStateResponse nativeOriginalClockResourceResponse
  dsimp only [nativeActualInitialState,NativeResourceTerm.ofLive,nativeResourceSeed]
  simp only [pow_zero,one_mul]
  congr 1
  funext σ
  simp only [NativeResourceTerm.value,NativeResourceTerm.scalar,
    List.map_nil,List.prod_nil,one_mul,NativeResourceMark.cut,nativeGeneratedSeed,
    NativeGeneratedTest.value,NativeGeneratedTest.edges,nativeGeneratedEdgeProduct,
    List.map_nil,List.nil_append,List.map_singleton,List.prod_singleton]
  rw [splitIndex_symm,nativeFreshAtSlot_split,splitIndex_self,Nat.min_eq_left hi]
  rw [(nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).restrict_at]
  rw [(nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).spin_at]

theorem actual_target_response_eq_four_iteration
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length) (ho : MassOrdered 0 as)
    (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    nativeActualTargetLongitudinalResponse M as i U=
      nativeActualMinimumFourResidualSum M hs hU W depth [st]+
      nativeActualOriginalContinuumCenteredFourGFrontier M as W i star U hi hs hU depth-
      nativeActualMinimumFourStateResponse M U W st.freeze := by
  dsimp only
  have H:=actual_minimum_initial_four_resource_finite_iteration M as W i star U hi hs hU ho hW hstarK depth
  dsimp only at H
  rw [←actual_target_response_eq_initial_four_state M as ho i star U (hi.trans (hs.le.trans hU)) W] at H
  linarith only [H]

end OAI.SKFluctuations.Cavity
