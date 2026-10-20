module

public import ComparisonSignedCavityActualInitialNormalizedResidual
public import ComparisonSignedCavityActualInitialLongitudinalOnCutsAlong
public import ComparisonSignedCavityActualInitialFrozenChildEnvelopeAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualInitialThermalSourceCategories : List NativeActualOtherSourceCategory :=
  [.secondLow,.higherTaylor,.jointLowTwoHigh,.jointLowRestoration,.fourGLowRestoration]

def nativeActualInitialThermalCategoryEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialThermalSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum M U W rows cat|/(chi*K star))).sum

theorem actual_initial_pending_eq_longitudinal_add_thermal
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    nativeActualInitialPendingCategoryEnvelope M U W rows=
      nativeActualInitialLongitudinalEnvelope M U W rows+
      nativeActualInitialThermalCategoryEnvelope M U W rows := by
  simp only [nativeActualInitialPendingCategoryEnvelope,nativeActualInitialLongitudinalEnvelope,
    nativeActualInitialThermalCategoryEnvelope,nativeActualInitialPendingSourceCategories,
    nativeActualInitialThermalSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

def nativeActualInitialPairFeedbackEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  ((List.range depth).map (fun d=>
    |1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *
      |nativeActualFourPairSum M U W (nativeActualMinimumFourCenteredForest M hs hU W d rows)|/
        (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_initial_normalized_residual_envelope_eq
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let forest:=fun d=>nativeActualMinimumFourCenteredForest M hs hU W d rows
    nativeActualInitialNormalizedResidualEnvelope M hs hU W Temp cK depth rows=
      nativeActualInitialPairFeedbackEnvelope M hs hU W Temp cK depth rows+
      nativeActualFourFrozenChildResidualEnvelope M hs hU W depth rows+
      ((List.range depth).map (fun d=>nativeActualInitialSavedNonLowEnvelope M U W (forest d))).sum+
      ((List.range depth).map (fun d=>nativeActualThreeGammaCategoryEnvelope M U W (forest d))).sum+
      ((List.range depth).map (fun d=>nativeActualInitialLongitudinalEnvelope M U W (forest d))).sum+
      ((List.range depth).map (fun d=>nativeActualInitialThermalCategoryEnvelope M U W (forest d))).sum := by
  dsimp only
  simp only [nativeActualInitialNormalizedResidualEnvelope,nativeActualInitialNormalizedLevelEnvelope,
    actual_initial_pending_eq_longitudinal_add_thermal,add_assoc,List.sum_map_add,
    nativeActualInitialPairFeedbackEnvelope,nativeActualFourFrozenChildResidualEnvelope]

theorem actual_minimum_initial_residual_abs_le_six_inputs
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hrows : ∀Q∈rows,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (depth : ℕ) {Bpair Bfrozen Bnonlow Bgamma Blong Bthermal : ℝ}
    (Hpair : nativeActualInitialPairFeedbackEnvelope M hs hU W Temp cK depth rows ≤ Bpair)
    (Hfrozen : nativeActualFourFrozenChildResidualEnvelope M hs hU W depth rows ≤ Bfrozen)
    (Hnonlow : ((List.range depth).map (fun d=>nativeActualInitialSavedNonLowEnvelope M U W
      (nativeActualMinimumFourCenteredForest M hs hU W d rows))).sum ≤ Bnonlow)
    (Hgamma : ((List.range depth).map (fun d=>nativeActualThreeGammaCategoryEnvelope M U W
      (nativeActualMinimumFourCenteredForest M hs hU W d rows))).sum ≤ Bgamma)
    (Hlong : ((List.range depth).map (fun d=>nativeActualInitialLongitudinalEnvelope M U W
      (nativeActualMinimumFourCenteredForest M hs hU W d rows))).sum ≤ Blong)
    (Hthermal : ((List.range depth).map (fun d=>nativeActualInitialThermalCategoryEnvelope M U W
      (nativeActualMinimumFourCenteredForest M hs hU W d rows))).sum ≤ Bthermal) :
    |nativeActualMinimumFourResidualSum M hs hU W depth rows| ≤
      Bpair+Bfrozen+Bnonlow+Bgamma+Blong+Bthermal := by
  have H:=actual_minimum_four_residual_abs_le_initial_normalized_envelope M htotal hW hcK ho
    hi hs hU hstarK rows hrows depth
  rw [actual_initial_normalized_residual_envelope_eq] at H
  exact H.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add Hpair Hfrozen) Hnonlow)
    Hgamma) Hlong) Hthermal)

end OAI.SKFluctuations.Cavity
