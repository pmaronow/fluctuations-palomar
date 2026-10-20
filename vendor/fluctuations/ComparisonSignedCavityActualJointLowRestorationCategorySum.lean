module

public import ComparisonSignedCavityActualFourJointLowRestorationProfile
public import ComparisonSignedCavityActualFourForestNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000

theorem actual_joint_LOW_restoration_category_signed_sum_abs_le_error_sum
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length) {W cK : ℝ} (hW : 0 < W) (hcK : 0 < cK)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast M U Q .jointLowRestoration)).sum|/
      (chi*K star) ≤ (xs.map (fun Q=>|nativeActualOriginalFourJointLowRestorationError M U W Q|)).sum := by
  dsimp only
  obtain ⟨hden,_,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks M hCf HS hxs hW hcK ho hs hU hstarK
  have H:=native_abs_sum_map_le xs (nativeActualOriginalFourJointLowRestorationError M U W)
  unfold nativeActualOriginalFourJointLowRestorationError at H
  dsimp only at H
  rw [List.sum_map_mul_left,abs_mul,abs_of_pos (div_pos zero_lt_one hden)] at H
  simpa only [nativeActualOriginalFourJointLowRestorationError,one_div,one_mul,mul_comm,div_eq_mul_inv] using H

end OAI.SKFluctuations.Cavity
