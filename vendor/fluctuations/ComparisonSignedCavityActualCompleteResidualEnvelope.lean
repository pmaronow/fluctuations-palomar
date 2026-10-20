module

public import ComparisonSignedCavityActualConstantSourceCategoryReduction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualCompleteFourLevelEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length) (W Temp cK : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=Real.exp (-4*Temp)*cK*W
  |1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *|nativeActualFourPairSum M U W xs|/den+
    |nativeActualFourFrozenChildSum M hs hU W xs|+
    ((K star/W)/(Real.exp (-4*Temp)*cK))*
      ((xs.map (fun Q=>|nativeActualOriginalFourGaCurrentError M U W Q|)).sum+
        (xs.map (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum)+
    (xs.map (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum+
    (nativeActualOtherSourceCategories.map
      (fun cat=>|nativeActualFourOtherCategorySum M U W xs cat|)).sum/den

theorem actual_minimum_four_level_abs_le_complete_envelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term) :
    |(xs.map (nativeActualOriginalFourRecursionError M hs hU W)).sum|≤
      nativeActualCompleteFourLevelEnvelope M hs hU W Temp cK xs := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have HK : K star≤(K star/W)*W:=le_of_eq (by field_simp)
  have HE:=actual_minimum_four_recursion_error_sum_first_high_abs_le M htotal hW hcK ho
    hi hs hU hstarK xs hxs le_rfl le_rfl le_rfl le_rfl
  have HC:=actual_minimum_four_other_source_closed_categories_abs_le M
    htotal hW hcK hcK ho hi hs hU hstarK HK xs hxs le_rfl le_rfl le_rfl
  dsimp only at HE
  dsimp only [nativeActualCompleteFourLevelEnvelope]
  have H:=add_le_add_left HC
    (|1-(M.bf (partitionPoint 0 as star):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0^2| *
        |nativeActualFourPairSum M U W xs|/(Real.exp (-4*Temp)*cK*W)+
      |nativeActualFourFrozenChildSum M hs hU W xs|)
  apply HE.trans
  convert H using 1 <;> dsimp only [K] <;> ring

def nativeActualCompleteFourResidualEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star<U) (hU : U≤as.length) (W Temp cK : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun j=>nativeActualCompleteFourLevelEnvelope M hs hU W Temp cK
    (nativeActualMinimumFourCenteredForest M hs hU W j xs))).sum

theorem actual_minimum_four_residual_abs_le_complete_envelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (depth : ℕ) :
    |nativeActualMinimumFourResidualSum M hs hU W depth xs|≤
      nativeActualCompleteFourResidualEnvelope M hs hU W Temp cK depth xs := by
  unfold nativeActualMinimumFourResidualSum nativeActualCompleteFourResidualEnvelope
  apply (native_abs_sum_map_le _ _).trans
  apply List.sum_le_sum
  intro j _
  exact actual_minimum_four_level_abs_le_complete_envelope M htotal hW hcK ho hi hs hU hstarK
    (nativeActualMinimumFourCenteredForest M hs hU W j xs)
    (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ j xs hxs)

end OAI.SKFluctuations.Cavity
