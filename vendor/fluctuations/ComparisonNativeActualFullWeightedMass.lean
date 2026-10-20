module

public import ComparisonNativeActualHighFlatOffFloorWeightedAlong
public import ComparisonNativeActualOriginalFloorMass
public import ComparisonNativeActualNormalizedScalarGap
public import ComparisonNativeActualInheritedBareError
public import ComparisonScalarFloorCharge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

 theorem original_weighted_mismatch_integrable (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (mu : Measure ParisiFinite.OrderPoint) [IsFiniteMeasure mu] (x : ℝ) :
    Integrable (fun w : ParisiFinite.OrderPoint =>
      laplaceComparisonStrength M.context.d M.lam (M.R w)*
        (orderedPathS (n+1) M.bf M.hf w-M.R w)/x^3) mu := by
  have hrm : Measurable (fun w : ParisiFinite.OrderPoint => M.R w) :=
    (comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha).measurable.comp measurable_subtype_coe
  have hsm : Measurable (fun w : ParisiFinite.OrderPoint => orderedPathS (n+1) M.bf M.hf w) :=
    (show Monotone (fun w : ParisiFinite.OrderPoint => orderedPathS (n+1) M.bf M.hf w) from
      fun u v huv => M.mass_mean_monotone u.property v.property huv).measurable
  have hem := (laplaceComparisonStrength_contDiff M.context.d M.lam).continuous.measurable.comp hrm
  have hi : Integrable (fun w : ParisiFinite.OrderPoint =>
      laplaceComparisonStrength M.context.d M.lam (M.R w)*
        (orderedPathS (n+1) M.bf M.hf w-M.R w)) mu := by
    apply (integrable_const (2*M.lam)).mono' (hem.mul (hsm.sub hrm)).aestronglyMeasurable
    filter_upwards [] with w
    have hs := M.mass_mean_unit_bounds w.property
    have hr := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (w:ℝ)
    have he := laplaceComparisonStrength_pos M.context.d M.hlam (M.R w)
    have hel := laplaceComparisonStrength_le M.context.d M.hlam.le (M.R w)
    have hm : |orderedPathS (n+1) M.bf M.hf w-M.R w| ≤ 2 := by
      apply abs_le.mpr; constructor <;> linarith only [hs.1,hs.2,hr.1,hr.2]
    change |laplaceComparisonStrength M.context.d M.lam (M.R w)*
      (orderedPathS (n+1) M.bf M.hf w-M.R w)| ≤ 2*M.lam
    rw [abs_mul,abs_of_pos he]
    exact (mul_le_mul_of_nonneg_left hm he.le).trans (by linarith only [hel])
  exact hi.div_const _

 theorem Potential.original_off_floor_weighted_integral_exact (p : M.Potential)
    {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    (∫w : ParisiFinite.OrderPoint in p.originalOrderFloorᶜ,
      |laplaceComparisonStrength M.context.d M.lam (M.R w)*
        (orderedPathS (n+1) M.bf M.hf w-M.R w)/M.xs^3|
        ∂comparisonNormalizedClockMass M.xs v) =
      (∫u in 0..v,p.offFloorWeightedDiscrepancy u)/M.xs^4 := by
  rw [← integral_indicator p.originalOrderFloor_measurable.compl]
  have heq : (fun w : ParisiFinite.OrderPoint => p.originalOrderFloorᶜ.indicator
      (fun w => |laplaceComparisonStrength M.context.d M.lam (M.R w)*
        (orderedPathS (n+1) M.bf M.hf w-M.R w)/M.xs^3|) w) =
      fun w : ParisiFinite.OrderPoint => |p.offFloorWeightedDiscrepancy w/M.xs^3| := by
    funext w
    by_cases H : w ∈ p.originalOrderFloor
    · have HP : p.positiveMassMask w=1 := by
        rw [← p.originalOrderFloor_indicator w,indicator_of_mem H]
      rw [indicator_of_notMem (show w ∉ p.originalOrderFloorᶜ from not_not.mpr H)]
      simp only [Potential.offFloorWeightedDiscrepancy, HP, sub_self, mul_zero, zero_div, abs_zero]
    · have HP : p.positiveMassMask w=0 := by
        rw [← p.originalOrderFloor_indicator w,indicator_of_notMem H]
      rw [indicator_of_mem (show w ∈ p.originalOrderFloorᶜ from H)]
      simp only [Potential.offFloorWeightedDiscrepancy, HP, sub_zero, mul_one, abs_div, abs_abs]
  rw [heq,comparison_normalized_cubic_residual_integral_exact _ M.hxs hv]
  simp_rw [abs_of_nonneg (p.offFloorWeightedDiscrepancy_nonneg _)]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
