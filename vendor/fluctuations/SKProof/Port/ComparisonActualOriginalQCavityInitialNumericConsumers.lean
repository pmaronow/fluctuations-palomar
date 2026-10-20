module

public import ComparisonSignedCavityActualInitialFullResidualPrefixSource
public import SKProof.Port.ComparisonActualOriginalQCavityCategoryReduction
public import SKProof.Port.ComparisonActualOriginalQSquareInitialFrozenResponse
public import SKProof.Port.ComparisonActualOriginalQCavityCategoryInterfaces
public import SKProof.Port.ComparisonActualOriginalQLowB0OriginalConstantConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0FullModulusConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQLowB0WeightedConsumerSourceAlong
public import SKProof.Port.ComparisonActualOriginalQCavityEarlyNumericConsumers
public import SKProof.Port.ComparisonActualOriginalQCavityTargetReadoutConsumers
public import SKProof.Port.ComparisonActualOriginalQPullbackFourProducers
public import SKProof.Port.ComparisonActualOriginalQCavityConsumerPrimitives
public import SKProof.Port.ComparisonActualOriginalQComparableBandStarBond
public import SKProof.Port.ComparisonActualOriginalQSquareConsumerActualSharpFourTerminalAlong
public import SKProof.Port.ComparisonActualOriginalQTargetRefinement

@[expose] public section
noncomputable section
set_option autoImplicit false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualInitialSavedNonLowEnvelope_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |nativeActualFourFirstHighErrorSum_original_q M U W rows|+
    |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q)).sum|/(chi*K star)+
    |nativeActualFourOtherCategorySum_original_q M U W rows .deletedSite|/(chi*K star)

theorem actual_initial_saved_nonLOW_envelope_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : ActualOriginalQSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
    {W cK BG BR BF BD : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hrows : ∀Q∈rows,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (HG : (rows.map (fun Q=>|nativeActualOriginalFourGaCurrentError_original_q M U W Q|)).sum ≤ BG)
    (HR : (rows.map (fun Q=>|nativeActualOriginalFourGaRestorationError_original_q M U W Q|)).sum ≤ BR)
    (HF : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError_original_q M U W Q|)).sum ≤ BF)
    (HD :
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum_original_q M U W rows .deletedSite|/(chi*K star) ≤ BD) :
    nativeActualInitialSavedNonLowEnvelope_original_q M U W rows ≤ BF+BG+BR+BD := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks_original_q
    M hCf HS hxs hW hcK ho hs hU hstarK
  change 0 < den at hden
  have Hrow Q (hQ : Q∈rows) :
      |(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q| ≤
        den*(|nativeActualOriginalFourGaCurrentError_original_q M U W Q|+
          |nativeActualOriginalFourGaRestorationError_original_q M U W Q|):=by
    have HE:=actual_minimum_four_Ga_error_eq_current_add_restoration_original_q M Q (hrows Q hQ) hi hs ho W
    have HI : (W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q=
        -den*nativeActualOriginalFourGaError_original_q M U W Q:=by
      unfold nativeActualOriginalFourGaError_original_q
      dsimp only
      change _ = -den*(-((W⁻¹)^Q.generation/den)*_)
      field_simp [hden.ne']
    rw [HI,abs_mul,abs_neg,abs_of_pos hden,HE]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hden.le
  have HGa : |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q)).sum|/den ≤ BG+BR:=by
    apply (div_le_iff₀ hden).mpr
    apply (native_abs_sum_map_le rows _).trans
    apply (List.sum_le_sum Hrow).trans
    rw [List.sum_map_mul_left,List.sum_map_add]
    exact (mul_le_mul_of_nonneg_left (add_le_add HG HR) hden.le).trans_eq (mul_comm _ _)
  have HFsum : |nativeActualFourFirstHighErrorSum_original_q M U W rows| ≤ BF:=
    (native_abs_sum_map_le rows _).trans HF
  have H:=add_le_add (add_le_add HFsum HGa) HD
  simpa only [nativeActualInitialSavedNonLowEnvelope_original_q,den,chi,K,add_assoc] using H

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualInitialPendingCategoryEnvelope_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialPendingSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W rows cat|/(chi*K star))).sum

def nativeActualInitialNormalizedLevelEnvelope_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |1-(M.sweepBf (partitionPoint 0 as star):ℝ)*chi^2| *|nativeActualFourPairSum_original_q M U W rows|/
      (Real.exp (-4*Temp)*cK*W)+
    |nativeActualFourFrozenChildSum_original_q M hs hU W rows|+
    nativeActualInitialSavedNonLowEnvelope_original_q M U W rows+
    nativeActualThreeGammaCategoryEnvelope_original_q M U W rows+
    nativeActualInitialPendingCategoryEnvelope_original_q M U W rows

theorem actual_initial_source_categories_partition_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualFourFirstHighErrorSum_original_q M U W rows|+
      |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q)).sum|/(chi*K star)+
      (nativeActualOtherSourceCategories.map
        (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W rows cat|/(chi*K star))).sum =
    nativeActualInitialSavedNonLowEnvelope_original_q M U W rows+
      nativeActualThreeGammaCategoryEnvelope_original_q M U W rows+
      nativeActualInitialPendingCategoryEnvelope_original_q M U W rows := by
  simp only [nativeActualInitialSavedNonLowEnvelope_original_q,nativeActualThreeGammaCategoryEnvelope_original_q,
    nativeActualInitialPendingCategoryEnvelope_original_q,nativeActualInitialPendingSourceCategories,
    nativeActualOtherSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

theorem actual_minimum_four_level_abs_le_initial_normalized_envelope_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hrows : ∀Q∈rows,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term) :
    |(rows.map (nativeActualOriginalFourRecursionError_original_q M hs hU W)).sum| ≤
      nativeActualInitialNormalizedLevelEnvelope_original_q M hs hU W Temp cK rows := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  let den0:=Real.exp (-4*Temp)*cK*W
  let J:=1-(M.sweepBf (partitionPoint 0 as star):ℝ)*chi^2
  obtain ⟨hden,_,hdenLower⟩:=actual_minimum_four_denominator_bounds_original_q M htotal hW hcK ho hs hU hstarK
  change 0 < den at hden
  change den0 ≤ den at hdenLower
  have hden0 : 0 < den0:=by dsimp only [den0];positivity
  have Hpair : |J/den*nativeActualFourPairSum_original_q M U W rows| ≤
      |J| *|nativeActualFourPairSum_original_q M U W rows|/den0:=by
    rw [abs_mul,abs_div,abs_of_pos hden]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hden0 hdenLower
  have Hother : |(1/den)*nativeActualFourOtherSourceErrorSum_original_q M U W rows| ≤
      |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q)).sum|/den+
      (nativeActualOtherSourceCategories.map (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W rows cat|/den)).sum:=by
    rw [one_div,mul_comm,←div_eq_mul_inv,abs_div,abs_of_pos hden,
      native_actual_four_other_source_sum_eq_Ga_add_categories_original_q]
    apply (div_le_div_of_nonneg_right (abs_add_le _ _) hden.le).trans
    rw [add_div]
    apply add_le_add le_rfl
    have H:=div_le_div_of_nonneg_right
      (native_abs_sum_map_le nativeActualOtherSourceCategories (nativeActualFourOtherCategorySum_original_q M U W rows)) hden.le
    simpa only [div_eq_mul_inv,List.sum_map_mul_right] using H
  rw [actual_minimum_four_recursion_error_sum_first_high_decomposition_original_q M rows hrows hi hs ho hU W]
  have Hsub (a b : ℝ) : |a-b| ≤ |a|+|b|:=by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  have HB : |J/den*nativeActualFourPairSum_original_q M U W rows+
      nativeActualFourFirstHighErrorSum_original_q M U W rows-
      (1/den)*nativeActualFourOtherSourceErrorSum_original_q M U W rows-
      nativeActualFourFrozenChildSum_original_q M hs hU W rows| ≤
      (|J| *|nativeActualFourPairSum_original_q M U W rows|/den0+
        |nativeActualFourFirstHighErrorSum_original_q M U W rows|)+
      (|(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast_original_q M U Q)).sum|/den+
        (nativeActualOtherSourceCategories.map (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W rows cat|/den)).sum)+
      |nativeActualFourFrozenChildSum_original_q M hs hU W rows| :=
    (Hsub _ _).trans (add_le_add
      ((Hsub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add Hpair le_rfl)) Hother)) le_rfl)
  apply HB.trans_eq
  dsimp only [nativeActualInitialNormalizedLevelEnvelope_original_q]
  have HE:=actual_initial_source_categories_partition_original_q M U W rows
  dsimp only at HE
  dsimp only [J,den,den0,chi,K]
  linarith [HE]

def nativeActualInitialNormalizedResidualEnvelope_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun d=>nativeActualInitialNormalizedLevelEnvelope_original_q M hs hU W Temp cK
    (nativeActualMinimumFourCenteredForest_original_q M hs hU W d rows))).sum

theorem actual_minimum_four_residual_abs_le_initial_normalized_envelope_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hrows : ∀Q∈rows,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (depth : ℕ) :
    |nativeActualMinimumFourResidualSum_original_q M hs hU W depth rows| ≤
      nativeActualInitialNormalizedResidualEnvelope_original_q M hs hU W Temp cK depth rows := by
  unfold nativeActualMinimumFourResidualSum_original_q nativeActualInitialNormalizedResidualEnvelope_original_q
  apply (native_abs_sum_map_le _ _).trans
  apply List.sum_le_sum
  intro d _
  exact actual_minimum_four_level_abs_le_initial_normalized_envelope_original_q M htotal hW hcK ho hi hs hU hstarK
    (nativeActualMinimumFourCenteredForest_original_q M hs hU W d rows)
    (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ d rows hrows)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualFourFrozenChildResidualEnvelope_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  ((List.range depth).map (fun d=>|nativeActualFourFrozenChildSum_original_q M hs hU W
    (nativeActualMinimumFourCenteredForest_original_q M hs hU W d xs)|)).sum

def ActualInitialFrozenChildEnvelopeOnGivenCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Cmass : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star<U,∃hU : U ≤ as.length,
      ∀(i : ℕ) (hi : i ≤ star) (x : ℝ),(M n).xs ≤ x → x ≤ W n →
        partitionPoint 0 as i ≤ Cmass*x →
        nativeActualFourFrozenChildResidualEnvelope_original_q (M n) hs hU (W n) depth
          [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))] ≤
            err n*(x*(M n).xs^2)

theorem actual_initial_frozen_child_envelope_of_levels_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Cmass c cK A : ℝ}
    (depth : ℕ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry_original_q (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A)
    (Hlevels : ∀d : ℕ,d<depth → ActualOriginalFourFrozenChildLevelSavingAlong_original_q d Cmass M W w) :
    ActualInitialFrozenChildEnvelopeOnGivenCutsAlong_original_q depth Cmass
      (fun n=>(depth:ℝ)*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)) M W w high outer := by
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>Hlevels d.val d.isLt)
  filter_upwards [HN,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hstar hret hmesh)
  filter_upwards [Hgrid] with jGrid hj
  dsimp only at hj ⊢
  obtain ⟨hs,HUV,HV,_,_,_,_,_,_,_,_,_,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  refine ⟨hs,hU,?_⟩
  intro i hi x hxsx hxW hmass
  unfold nativeActualFourFrozenChildResidualEnvelope_original_q
  apply (List.sum_le_sum (fun d hd=>hj ⟨d,List.mem_range.mp hd⟩ _ i hi hs hU x hxsx hxW hmass)).trans_eq
  simp only [List.map_const',List.length_range,List.sum_replicate,nsmul_eq_mul]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualInitialThermalCategoryEnvelope_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialThermalSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W rows cat|/(chi*K star))).sum

theorem actual_initial_pending_eq_longitudinal_add_thermal_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    nativeActualInitialPendingCategoryEnvelope_original_q M U W rows=
      nativeActualInitialLongitudinalEnvelope_original_q M U W rows+
      nativeActualInitialThermalCategoryEnvelope_original_q M U W rows := by
  simp only [nativeActualInitialPendingCategoryEnvelope_original_q,nativeActualInitialLongitudinalEnvelope_original_q,
    nativeActualInitialThermalCategoryEnvelope_original_q,nativeActualInitialPendingSourceCategories,
    nativeActualInitialThermalSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

def nativeActualInitialPairFeedbackEnvelope_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  ((List.range depth).map (fun d=>
    |1-(M.sweepBf (partitionPoint 0 as star):ℝ)*chi^2| *
      |nativeActualFourPairSum_original_q M U W (nativeActualMinimumFourCenteredForest_original_q M hs hU W d rows)|/
        (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_initial_normalized_residual_envelope_eq_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let forest:=fun d=>nativeActualMinimumFourCenteredForest_original_q M hs hU W d rows
    nativeActualInitialNormalizedResidualEnvelope_original_q M hs hU W Temp cK depth rows=
      nativeActualInitialPairFeedbackEnvelope_original_q M hs hU W Temp cK depth rows+
      nativeActualFourFrozenChildResidualEnvelope_original_q M hs hU W depth rows+
      ((List.range depth).map (fun d=>nativeActualInitialSavedNonLowEnvelope_original_q M U W (forest d))).sum+
      ((List.range depth).map (fun d=>nativeActualThreeGammaCategoryEnvelope_original_q M U W (forest d))).sum+
      ((List.range depth).map (fun d=>nativeActualInitialLongitudinalEnvelope_original_q M U W (forest d))).sum+
      ((List.range depth).map (fun d=>nativeActualInitialThermalCategoryEnvelope_original_q M U W (forest d))).sum := by
  dsimp only
  simp only [nativeActualInitialNormalizedResidualEnvelope_original_q,nativeActualInitialNormalizedLevelEnvelope_original_q,
    actual_initial_pending_eq_longitudinal_add_thermal_original_q,add_assoc,List.sum_map_add,
    nativeActualInitialPairFeedbackEnvelope_original_q,nativeActualFourFrozenChildResidualEnvelope_original_q]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualHistoryInitialSavedNonLowOnGivenCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        nativeActualInitialSavedNonLowEnvelope_original_q (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
            [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length)
              seedMass (by omega)]) ≤ err n*(M n).xs^3

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualInitialResidualModuloThermalOnStrongCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail))
        pre.length (pre.length+mid.length) 0 (by omega)
      |nativeActualMinimumFourResidualSum_original_q (M n) hs hU (W n) depth [st]| ≤ err n*(M n).xs^3+
        ((List.range depth).map (fun d=>nativeActualInitialThermalCategoryEnvelope_original_q (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) d [st]))).sum

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualInitialFullB0ResidualEnvelope_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  ((List.range depth).map (fun d=>|nativeActualFourOtherCategorySum_original_q M U W
    (nativeActualMinimumFourCenteredForest_original_q M hs hU W d xs) .secondLow|/(chi*K star))).sum

def nativeActualInitialRestThermalCategoryEnvelope_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialRestThermalSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W rows cat|/(chi*K star))).sum

theorem actual_initial_thermal_residual_eq_full_B0_add_rest_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (hs : star < U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    ((List.range depth).map (fun d=>nativeActualInitialThermalCategoryEnvelope_original_q M U W
      (nativeActualMinimumFourCenteredForest_original_q M hs hU W d rows))).sum=
    nativeActualInitialFullB0ResidualEnvelope_original_q M hs hU W depth rows+
      ((List.range depth).map (fun d=>nativeActualInitialRestThermalCategoryEnvelope_original_q M U W
        (nativeActualMinimumFourCenteredForest_original_q M hs hU W d rows))).sum := by
  simp only [nativeActualInitialThermalCategoryEnvelope_original_q,nativeActualInitialThermalSourceCategories,
    nativeActualInitialRestThermalCategoryEnvelope_original_q,nativeActualInitialRestThermalSourceCategories,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,nativeActualInitialFullB0ResidualEnvelope_original_q,
    List.sum_map_add]

def ActualInitialResidualFourThermalModulusOnStrongCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail))
        pre.length (pre.length+mid.length) 0 (by omega)
      |nativeActualMinimumFourResidualSum_original_q (M n) hs hU (W n) depth [st]| ≤ Ci*(M n).xs^2*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+1/(dim n+1:ℕ))+
        err n*(M n).xs^3+
        ((List.range depth).map (fun d=>nativeActualInitialRestThermalCategoryEnvelope_original_q (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) d [st]))).sum

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 50000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualInitialTwoThermalCategoryEnvelope_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (nativeActualInitialTwoThermalSourceCategories.map
    (fun cat=>|nativeActualFourOtherCategorySum_original_q M U W rows cat|/(chi*K star))).sum

theorem native_actual_initial_four_thermal_envelope_eq_two_add_joint_HIGH_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualInitialRestThermalCategoryEnvelope_original_q M U W rows=
      nativeActualInitialTwoThermalCategoryEnvelope_original_q M U W rows+
      |nativeActualFourOtherCategorySum_original_q M U W rows .jointLowTwoHigh|/(chi*K star)+
      |nativeActualFourOtherCategorySum_original_q M U W rows .fourGLowRestoration|/(chi*K star) := by
  simp only [nativeActualInitialRestThermalCategoryEnvelope_original_q,nativeActualInitialRestThermalSourceCategories,
    nativeActualInitialTwoThermalCategoryEnvelope_original_q,nativeActualInitialTwoThermalSourceCategories,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

theorem native_actual_initial_category_bound_star_transport_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star star' U depth : ℕ} {W B seedMass : ℝ}
    {cat : NativeActualOtherSourceCategory}
    (hs : star < U) (hs' : star' < U) (hU : U ≤ as.length) (hi : i ≤ as.length)
    (hstar : star=star')
    (H : let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
         let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
         |nativeActualFourOtherCategorySum_original_q M U W
           (nativeActualMinimumFourCenteredForest_original_q M hs hU W depth
             [nativeActualInitialState as i star seedMass hi]) cat|/(chi*K star) ≤ B) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualFourOtherCategorySum_original_q M U W
      (nativeActualMinimumFourCenteredForest_original_q M hs' hU W depth
        [nativeActualInitialState as i star' seedMass hi]) cat|/(chi*K star') ≤ B := by
  subst star'
  exact H

def ActualInitialResidualTwoThermalModulusOnStrongCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail))
        pre.length (pre.length+mid.length) 0 (by omega)
      |nativeActualMinimumFourResidualSum_original_q (M n) hs hU (W n) depth [st]| ≤ Ci*(M n).xs^2*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+1/(dim n+1:ℕ))+
        err n*(M n).xs^3+
        ((List.range depth).map (fun d=>nativeActualInitialTwoThermalCategoryEnvelope_original_q (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) d [st]))).sum
end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem native_actual_initial_full_residual_reindex_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as as' : List PositiveMass} {i i' star star' U depth : ℕ} {W : ℝ}
    (has : as'=as) (hindex : i'=i) (hstar : star'=star)
    (hs' : star'<U) (hs : star<U) (hU' : U ≤ as'.length) (hU : U ≤ as.length)
    (hi' : i' ≤ as'.length) (hi : i ≤ as.length) :
    nativeActualMinimumFourResidualSum_original_q M hs' hU' W depth
        [nativeActualInitialState as' i' star' 0 hi']=
      nativeActualMinimumFourResidualSum_original_q M hs hU W depth
        [nativeActualInitialState as i star 0 hi] := by
  subst as'
  subst i'
  subst star'
  rfl

def ActualInitialResidualFullModulusOnStrongCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail))
        pre.length (pre.length+mid.length) 0 (by omega)
      |nativeActualMinimumFourResidualSum_original_q (M n) hs hU (W n) depth [st]| ≤ Ci*(M n).xs^2*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+1/(dim n+1:ℕ))+
        err n*(M n).xs^3

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem ActualInitialResidualFullModulusOnStrongCutsAlong_original_q.to_retained_targets
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    {depth : ℕ} {A Atarget Ci : ℝ} {err : ℕ→ℝ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice} {high outer : ℕ→PositiveMass}
    (H : ActualInitialResidualFullModulusOnStrongCutsAlong_original_q depth A Ci err M W w high outer)
    (hA : Atarget ≤ A) :
    ActualInitialFullResidualOnRetainedTargetsAlong_original_q depth Atarget Ci err M W w high outer := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hn L us hus hret hmesh hstar hhigh houter hnodes] with jGrid hj
  dsimp only at hj ⊢
  intro i hi hs hU hmass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have hilen:i ≤ as.length:=hi.le.trans (hs.le.trans hU)
  obtain ⟨pre,mid,tail,hparts,hpre,hindex,hmid⟩:=
    native_actual_initial_retained_target_prefix_split as i star hi (hs.le.trans hU)
  have hmass':partitionPoint 0 as pre.length ≤ A*(M n).xs := by
    rw [hpre]
    exact hmass.trans (mul_le_mul_of_nonneg_right hA (M n).hxs.le)
  obtain ⟨hs',hU',Hbound⟩:=hj pre mid tail hparts hindex hmid hmass'
  have Hsource:=native_actual_initial_full_residual_reindex_original_q (M n) (W:=W n) (depth:=depth)
    hparts hpre hindex hs' hs hU' hU (by omega) hilen
  rw [Hsource] at Hbound
  simpa only [hpre] using Hbound

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem native_actual_initial_category_bound_partition_star_transport_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as bs : List PositiveMass} {i star star' U depth : ℕ} {W B seedMass : ℝ}
    {cat : NativeActualOtherSourceCategory}
    (hs : star < U) (hs' : star' < U) (hU : U ≤ as.length) (hU' : U ≤ bs.length)
    (hi : i ≤ as.length) (hi' : i ≤ bs.length)
    (hparts : as=bs) (hstar : star=star')
    (H : let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
         let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
         |nativeActualFourOtherCategorySum_original_q M U W
           (nativeActualMinimumFourCenteredForest_original_q M hs hU W depth
             [nativeActualInitialState as i star seedMass hi]) cat|/(chi*K star) ≤ B) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf bs
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks bs (relocatedClock U 0 K))).H 0 0
    |nativeActualFourOtherCategorySum_original_q M U W
      (nativeActualMinimumFourCenteredForest_original_q M hs' hU' W depth
        [nativeActualInitialState bs i star' seedMass hi']) cat|/(chi*K star') ≤ B := by
  subst bs
  subst star'
  exact H

def ActualInitialHigherTaylorOnStrongGivenCutsAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A Ci : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        let old:=pre++(mid++tail)
        let K:=nativeContinuumMixedClock (dim n) (M n).sweepBf (M n).sweepHf old
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum_original_q (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
            [nativeActualInitialState old pre.length (pre.length+mid.length) seedMass (by dsimp only [old];omega)])
          .higherTaylor|/(chi*K (pre.length+mid.length)) ≤
            Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).sweepBf (M n).sweepHf as pre.length+
              1/(dim n+1:ℕ))+err n*(M n).xs^3

end OAI.SKFluctuations.Cavity

