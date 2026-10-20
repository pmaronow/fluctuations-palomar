module

public import ComparisonSignedCavityActualInitialSavedNonLowEnvelope
public import ComparisonSignedCavityActualCompleteResidualEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualInitialPendingSourceCategories : List NativeActualOtherSourceCategory :=
  [.secondLow,.higherTaylor,.jointLowTwoHigh,.jointLowRestoration,
    .longitudinalLeft,.longitudinalRight,.fourGLowRestoration]

def nativeActualInitialPendingCategoryEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialPendingSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum M U W rows cat|/(chi*K star))).sum

def nativeActualInitialNormalizedLevelEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *|nativeActualFourPairSum M U W rows|/
      (Real.exp (-4*Temp)*cK*W)+
    |nativeActualFourFrozenChildSum M hs hU W rows|+
    nativeActualInitialSavedNonLowEnvelope M U W rows+
    nativeActualThreeGammaCategoryEnvelope M U W rows+
    nativeActualInitialPendingCategoryEnvelope M U W rows

theorem actual_initial_source_categories_partition
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualFourFirstHighErrorSum M U W rows|+
      |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast M U Q)).sum|/(chi*K star)+
      (nativeActualOtherSourceCategories.map
        (fun cat=>|nativeActualFourOtherCategorySum M U W rows cat|/(chi*K star))).sum =
    nativeActualInitialSavedNonLowEnvelope M U W rows+
      nativeActualThreeGammaCategoryEnvelope M U W rows+
      nativeActualInitialPendingCategoryEnvelope M U W rows := by
  simp only [nativeActualInitialSavedNonLowEnvelope,nativeActualThreeGammaCategoryEnvelope,
    nativeActualInitialPendingCategoryEnvelope,nativeActualInitialPendingSourceCategories,
    nativeActualOtherSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

theorem actual_minimum_four_level_abs_le_initial_normalized_envelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hrows : ∀Q∈rows,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term) :
    |(rows.map (nativeActualOriginalFourRecursionError M hs hU W)).sum| ≤
      nativeActualInitialNormalizedLevelEnvelope M hs hU W Temp cK rows := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  let den0:=Real.exp (-4*Temp)*cK*W
  let J:=1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2
  obtain ⟨hden,_,hdenLower⟩:=actual_minimum_four_denominator_bounds M htotal hW hcK ho hs hU hstarK
  change 0 < den at hden
  change den0 ≤ den at hdenLower
  have hden0 : 0 < den0:=by dsimp only [den0];positivity
  have Hpair : |J/den*nativeActualFourPairSum M U W rows| ≤
      |J| *|nativeActualFourPairSum M U W rows|/den0:=by
    rw [abs_mul,abs_div,abs_of_pos hden]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hden0 hdenLower
  have Hother : |(1/den)*nativeActualFourOtherSourceErrorSum M U W rows| ≤
      |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast M U Q)).sum|/den+
      (nativeActualOtherSourceCategories.map (fun cat=>|nativeActualFourOtherCategorySum M U W rows cat|/den)).sum:=by
    rw [one_div,mul_comm,←div_eq_mul_inv,abs_div,abs_of_pos hden,
      native_actual_four_other_source_sum_eq_Ga_add_categories]
    apply (div_le_div_of_nonneg_right (abs_add_le _ _) hden.le).trans
    rw [add_div]
    apply add_le_add le_rfl
    have H:=div_le_div_of_nonneg_right
      (native_abs_sum_map_le nativeActualOtherSourceCategories (nativeActualFourOtherCategorySum M U W rows)) hden.le
    simpa only [div_eq_mul_inv,List.sum_map_mul_right] using H
  rw [actual_minimum_four_recursion_error_sum_first_high_decomposition M rows hrows hi hs ho hU W]
  have Hsub (a b : ℝ) : |a-b| ≤ |a|+|b|:=by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  have HB : |J/den*nativeActualFourPairSum M U W rows+
      nativeActualFourFirstHighErrorSum M U W rows-
      (1/den)*nativeActualFourOtherSourceErrorSum M U W rows-
      nativeActualFourFrozenChildSum M hs hU W rows| ≤
      (|J| *|nativeActualFourPairSum M U W rows|/den0+
        |nativeActualFourFirstHighErrorSum M U W rows|)+
      (|(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast M U Q)).sum|/den+
        (nativeActualOtherSourceCategories.map (fun cat=>|nativeActualFourOtherCategorySum M U W rows cat|/den)).sum)+
      |nativeActualFourFrozenChildSum M hs hU W rows| :=
    (Hsub _ _).trans (add_le_add
      ((Hsub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add Hpair le_rfl)) Hother)) le_rfl)
  apply HB.trans_eq
  dsimp only [nativeActualInitialNormalizedLevelEnvelope]
  have HE:=actual_initial_source_categories_partition M U W rows
  dsimp only at HE
  dsimp only [J,den,den0,chi,K]
  linarith [HE]

def nativeActualInitialNormalizedResidualEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun d=>nativeActualInitialNormalizedLevelEnvelope M hs hU W Temp cK
    (nativeActualMinimumFourCenteredForest M hs hU W d rows))).sum

theorem actual_minimum_four_residual_abs_le_initial_normalized_envelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hrows : ∀Q∈rows,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (depth : ℕ) :
    |nativeActualMinimumFourResidualSum M hs hU W depth rows| ≤
      nativeActualInitialNormalizedResidualEnvelope M hs hU W Temp cK depth rows := by
  unfold nativeActualMinimumFourResidualSum nativeActualInitialNormalizedResidualEnvelope
  apply (native_abs_sum_map_le _ _).trans
  apply List.sum_le_sum
  intro d _
  exact actual_minimum_four_level_abs_le_initial_normalized_envelope M htotal hW hcK ho hi hs hU hstarK
    (nativeActualMinimumFourCenteredForest M hs hU W d rows)
    (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ d rows hrows)

end OAI.SKFluctuations.Cavity
