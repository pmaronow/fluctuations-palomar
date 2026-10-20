module

public import ComparisonSignedCavityActualInitialThreeGammaOnCutsAlong
public import ComparisonSignedCavityActualSharpSourceFirstHighAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualInitialSavedNonLowEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |nativeActualFourFirstHighErrorSum M U W rows|+
    |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast M U Q)).sum|/(chi*K star)+
    |nativeActualFourOtherCategorySum M U W rows .deletedSite|/(chi*K star)

theorem actual_initial_saved_nonLOW_envelope_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
    {W cK BG BR BF BD : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hrows : ∀Q∈rows,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (HG : (rows.map (fun Q=>|nativeActualOriginalFourGaCurrentError M U W Q|)).sum ≤ BG)
    (HR : (rows.map (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤ BR)
    (HF : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤ BF)
    (HD :
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum M U W rows .deletedSite|/(chi*K star) ≤ BD) :
    nativeActualInitialSavedNonLowEnvelope M U W rows ≤ BF+BG+BR+BD := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    M hCf HS hxs hW hcK ho hs hU hstarK
  change 0 < den at hden
  have Hrow Q (hQ : Q∈rows) :
      |(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast M U Q| ≤
        den*(|nativeActualOriginalFourGaCurrentError M U W Q|+
          |nativeActualOriginalFourGaRestorationError M U W Q|):=by
    have HE:=actual_minimum_four_Ga_error_eq_current_add_restoration M Q (hrows Q hQ) hi hs ho W
    have HI : (W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast M U Q=
        -den*nativeActualOriginalFourGaError M U W Q:=by
      unfold nativeActualOriginalFourGaError
      dsimp only
      change _ = -den*(-((W⁻¹)^Q.generation/den)*_)
      field_simp [hden.ne']
    rw [HI,abs_mul,abs_neg,abs_of_pos hden,HE]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hden.le
  have HGa : |(rows.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourGaContrast M U Q)).sum|/den ≤ BG+BR:=by
    apply (div_le_iff₀ hden).mpr
    apply (native_abs_sum_map_le rows _).trans
    apply (List.sum_le_sum Hrow).trans
    rw [List.sum_map_mul_left,List.sum_map_add]
    exact (mul_le_mul_of_nonneg_left (add_le_add HG HR) hden.le).trans_eq (mul_comm _ _)
  have HFsum : |nativeActualFourFirstHighErrorSum M U W rows| ≤ BF:=
    (native_abs_sum_map_le rows _).trans HF
  have H:=add_le_add (add_le_add HFsum HGa) HD
  simpa only [nativeActualInitialSavedNonLowEnvelope,den,chi,K,add_assoc] using H

end OAI.SKFluctuations.Cavity
