module

public import ComparisonNativeActualRegularThermalConcentrationAlong
public import ComparisonNativeActualInitialMassConcentration

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum

theorem regular_minimum_initial_mass_thermal_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(a n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (a n).alpha.val.val (a n).b (a n).h 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n =>
      (∫u in 0..C*W n,orderedPathB (dim n+1) (a n).bf (a n).hf u-
        (orderedPathS (dim n+1) (a n).bf (a n).hf u)^2)/(W n)^3) atTop (𝓝 0) := by
  obtain ⟨K,hK,hsmall⟩ := eventually_native_comparison_low_mass_thermal (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW := (hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have hW n : 0 < W n := (a n).hxs.trans_le (hxs n)
  apply tendsto_order.2
  constructor
  · intro b hb0
    filter_upwards [HW] with n hn
    have hw := hW n
    apply hb0.trans_le
    apply div_nonneg _ (pow_pos (hW n) 3).le
    apply intervalIntegral.integral_nonneg (by positivity)
    intro u hu
    exact (a n).actual_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans hn⟩
  · intro eps heps
    let c := min 1 (min (C/2) (eps/(16*K)))
    have hc : 0 < c := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
    have hc1 : c ≤ 1 := min_le_left _ _
    have hcC2 : c ≤ C/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hcC : c ≤ C := by linarith
    have hceps : c ≤ eps/(16*K) := (min_le_right _ _).trans (min_le_right _ _)
    have Hslab := regular_minimum_complete_mass_slab_thermal_ratio_tendsto_zero_along
      hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim a W hxs hWlim hclock c C hc hcC
    have Htail := Hslab.eventually (eventually_lt_nhds (show (0:ℝ) < eps/2 by positivity))
    filter_upwards [HW,Htail,((tendsto_add_atTop_nat 1).comp hdim).eventually hsmall]
      with n hnW hnTail hnSmall
    have hw := hW n
    have hxn := (a n).hxs
    let f := fun u => orderedPathB (dim n+1) (a n).bf (a n).hf u-
      (orderedPathS (dim n+1) (a n).bf (a n).hf u)^2
    have hcw : c*W n ≤ C*W n := mul_le_mul_of_nonneg_right hcC (hW n).le
    have hi := native_comparison_thermal_intervalIntegrable (a n)
    have hi0 : IntervalIntegrable f volume 0 (c*W n) := hi.mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ c*W n),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl (hcw.trans hnW))
    have hitail : IntervalIntegrable f volume (c*W n) (C*W n) := hi.mono_set (by
      rw [uIcc_of_le hcw,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (by positivity) hnW)
    have Hlow := hnSmall (a n) (c*W n) ⟨by positivity,hcw.trans hnW⟩
    have Hxs : (a n).xs+c*W n ≤ (1+c)*W n := by nlinarith [hxs n]
    have Hlow' : (∫u in 0..c*W n,f u)/(W n)^3 ≤ K*(1+c)^2*c := by
      apply (div_le_iff₀ (pow_pos (hW n) 3)).mpr
      apply Hlow.trans
      have Hp := pow_le_pow_left₀ (by positivity : 0 ≤ (a n).xs+c*W n) Hxs 2
      have Hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hp hK.le)
        (show 0 ≤ c*W n by positivity)
      convert Hmul using 1; ring
    have Hcoef : K*(1+c)^2*c ≤ eps/4 := by
      have Hp : (1+c)^2 ≤ (2:ℝ)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      have Hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hp hK.le) hc.le
      have He := (le_div_iff₀ (show 0 < 16*K by positivity)).mp hceps
      nlinarith
    have Htail' : (∫u in c*W n..C*W n,f u)/(W n)^3 < eps/2 := by
      rw [intervalIntegral.integral_of_le hcw,integral_Ioc_eq_integral_Ioo]
      exact hnTail
    change (∫u in 0..C*W n,f u)/(W n)^3 < eps
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hitail,add_div]
    linarith

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
