module

public import ComparisonSignedCavityActualFourLongitudinalRestorationProfile
public import ComparisonSignedCavityActualFourForestNumerics
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_longitudinal_category_signed_sum_abs_le_error_sum
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) (right : Bool) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast M U Q
      (nativeActualLongitudinalCategory right))).sum|/(chi*K star) ≤
      (xs.map (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks M hCf HS hxs hW hcK ho hs hU hstarK
  have Hsum : (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast M U Q
      (nativeActualLongitudinalCategory right))).sum=
      -den*(xs.map (fun Q=>nativeActualOriginalFourLongitudinalError M U W Q right)).sum := by
    rw [←List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro Q _
    rw [native_actual_four_longitudinal_contrast_eq_resources M U Q ho (hs.le.trans hU) right]
    dsimp only [nativeActualOriginalFourLongitudinalError,den,chi,K]
    ring
  dsimp only
  rw [Hsum,abs_mul,abs_neg,abs_of_pos hden]
  change den*|(xs.map (fun Q=>nativeActualOriginalFourLongitudinalError M U W Q right)).sum|/den ≤ _
  rw [mul_div_cancel_left₀ _ (ne_of_gt hden)]
  exact native_abs_sum_map_le xs (fun Q=>nativeActualOriginalFourLongitudinalError M U W Q right)

end OAI.SKFluctuations.Cavity
