module

public import ComparisonNativeActualInitialMassError
public import ComparisonNativeActualRegularInitialMassConcentration

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum

theorem regular_minimum_initial_mass_error_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(a n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀n,NativePullbackClockRegularity (a n).alpha.val.val (a n).b (a n).h 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n =>
      (∫u in 0..C*W n,Real.sqrt (orderedPathB (n+1) (a n).bf (a n).hf u-
        (orderedPathS (n+1) (a n).bf (a n).hf u)^2))/(W n)^2) atTop (𝓝 0) := by
  have Hthermal := regular_minimum_initial_mass_thermal_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt a W hxs hWlim hclock C hC
  have Hlimit := (Hthermal.const_mul C).sqrt
  simp only [mul_zero,Real.sqrt_zero] at Hlimit
  have HW := (hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Hlimit
  · filter_upwards [] with n
    have hw : 0 < W n := (a n).hxs.trans_le (hxs n)
    apply div_nonneg _ (sq_nonneg _)
    exact intervalIntegral.integral_nonneg (by positivity) (fun _ _ => Real.sqrt_nonneg _)
  · filter_upwards [HW] with n hnW
    have hw : 0 < W n := (a n).hxs.trans_le (hxs n)
    have hi := (native_comparison_thermal_intervalIntegrable (a n)).mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ C*W n),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    have Hsq := interval_integral_sqrt_sq_le (by positivity : 0 ≤ C*W n) hi
      (fun u hu => (a n).actual_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans hnW⟩)
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos (pow_pos hw 2) 2)).mpr
    convert Hsq using 1; field_simp

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
