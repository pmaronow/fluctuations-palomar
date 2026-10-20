module

public import ComparisonSignedCavityActualConstantSourceRetainedGammaAlong
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator
public import ComparisonSignedCavityActualConstantSourceCategoryReduction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000

theorem actual_retained_gamma_category_signed_sum_abs_le_error_sum
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualFourOtherCategorySum M U W xs .gammaRetained|/(chi*K star) ≤
      (xs.map (fun Q=>|nativeActualOriginalFourRetainedGammaError M U W Q|)).sum := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let den:=chi*K star
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    M hCf HS hxs hW hcK ho hs hU hstarK
  have Hsum : (xs.map (fun Q=>nativeActualOriginalFourRetainedGammaError M U W Q)).sum=
      -(nativeActualFourOtherCategorySum M U W xs .gammaRetained)/den := by
    calc
      _ = ((xs.map (fun Q=>(W⁻¹)^Q.generation*
          nativeActualOriginalFourOtherCategoryContrast M U Q .gammaRetained)).sum)*(-den⁻¹) := by
        rw [←List.sum_map_mul_right]
        apply congrArg List.sum
        apply List.map_congr_left
        intro Q _
        dsimp only [nativeActualOriginalFourRetainedGammaError,den,chi,K]
        ring
      _ = _ := by unfold nativeActualFourOtherCategorySum;ring
  dsimp only
  have H:=native_abs_sum_map_le xs (fun Q=>nativeActualOriginalFourRetainedGammaError M U W Q)
  rw [Hsum,abs_div,abs_neg,abs_of_pos hden] at H
  exact H

end OAI.SKFluctuations.Cavity
