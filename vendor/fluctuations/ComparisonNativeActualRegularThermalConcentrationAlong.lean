module

public import ComparisonNativeActualRegularMassSlabPolynomial
public import ComparisonNativeCavityRadiusGoodPoint

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 10000000

namespace NativeOverlapMinimum

theorem regular_minimum_complete_mass_slab_thermal_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(a n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (a n).alpha.val.val (a n).b (a n).h 0 1)
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) :
    Tendsto (fun n =>
      (∫u in Ioo (c*W n) (C*W n),orderedPathB (dim n+1) (a n).bf (a n).hf u-
        (orderedPathS (dim n+1) (a n).bf (a n).hf u)^2)/(W n)^3) atTop (𝓝 0) := by
  have Hbound := hdim.eventually (eventually_regular_minimum_complete_mass_slab_polynomial (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt c C hc hcC)
  have HW1 := hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  have HWC := (hWlim.const_mul C).eventually
    (eventually_le_nhds (by norm_num : C*(0:ℝ) < 1))
  have hrate : Tendsto (fun n : ℕ => ((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/2)))
      atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (half_pos (actualMassSavingExponent_pos hm hdelta))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  apply squeeze_zero'
    (by
      filter_upwards [HWC] with n hn
      have hW : 0 < W n := (a n).hxs.trans_le (hxs n)
      apply div_nonneg _ (pow_pos hW 3).le
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hui : u∈Icc (0:ℝ) 1 := ⟨(mul_pos hc hW).le.trans hu.1.le,hu.2.le.trans hn⟩
      have hr := comparisonSweepQuantile_bounds (a n).context.hc (a n).context.hk
        (a n).context.hkc (a n).context.hm (a n).context.hM (a n).alpha u
      have HD := (a n).cavityRadiusPointDefect_nonneg hr
      simpa only [Pi.zero_apply,cavityRadiusPointDefect,comparisonSweepQuantile_mass_spec
        (a n).context.hc (a n).context.hk (a n).context.hkc (a n).context.hm
        (a n).context.hM (a n).alpha hui] using HD)
    (by
      filter_upwards [Hbound,HW1,HWC,hclock] with n hn hn1 hnC hnclock
      have hW : 0 < W n := (a n).hxs.trans_le (hxs n)
      have Hle := hn (a n) hnclock (W n) (hxs n) hn1 hnC
      have hends : c*W n ≤ C*W n := mul_le_mul_of_nonneg_right hcC hW.le
      rw [intervalIntegral.integral_of_le hends, integral_Ioc_eq_integral_Ioo] at Hle
      exact Hle)
    hrate

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
