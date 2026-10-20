module

public import ComparisonNativeMassDyadicThermalBand
public import ComparisonNativeActualRegularIntermediateMassPhysicalDyad
public import ComparisonNativeActualRegularInitialMassError

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum

theorem regular_minimum_strong_initial_mass_error_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hclock : ∀n,NativePullbackClockRegularity (a n).alpha.val.val (a n).b (a n).h 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>
      (∫u in 0..min (C*(a n).canonicalDirectTestBandScale) 1,
        Real.sqrt (orderedPathB (n+1) (a n).bf (a n).hf u-
          (orderedPathS (n+1) (a n).bf (a n).hf u)^2))/(a n).xs^2)
      atTop (𝓝 0) := by
  let c := 2*cu*(Az+1)+1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcouter : 2*cu*(Az+1) ≤ c := by dsimp [c]; linarith
  have HX : Tendsto (fun n=>(a n).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(a n).hxs.le)
      (fun n=>(a n).canonical_direct_test_band_ge_scale) hWlim
  have Hinitial := regular_minimum_initial_mass_error_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt a (fun n=>(a n).xs)
    (fun _=>le_rfl) HX hclock c hc
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hdyad := eventually_actual_regular_strong_intermediate_mass_dyad
    (D:=D) (Cs:=Cs) C Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  have Hpow : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)^(-eta/2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (half_pos heta)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have Hroot := ((Hpow.const_mul C).mul_const (nativeIntermediateAccumulationConstant C)).sqrt
  simp only [mul_zero,zero_mul,Real.sqrt_zero] at Hroot
  have Htotal := Hinitial.add Hroot
  simp only [add_zero] at Htotal
  have HW1 := hWlim.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  have HW2 := (hWlim.const_mul (2*C)).eventually
    (eventually_le_nhds (show 2*C*(0:ℝ) < 1 by simp))
  have HX1 := (HX.const_mul c).eventually
    (eventually_le_nhds (show c*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [] with n
    apply div_nonneg _ (sq_nonneg _)
    exact intervalIntegral.integral_nonneg
      (le_min (mul_pos hC (a n).canonical_direct_test_band_pos).le zero_le_one)
      (fun _ _=>Real.sqrt_nonneg _)
  · filter_upwards [Hdyad,hsmall,HW1,HW2,HX1] with n hnDyad hnSmall hnW1 hnW2 hnX1
    have hW := (a n).canonical_direct_test_band_pos
    have htop : C*(a n).canonicalDirectTestBandScale ≤ 1 := by
      nlinarith [mul_pos hC hW]
    rw [min_eq_left htop]
    apply native_initial_plus_intermediate_error_ratio_le hc hC (a n).hxs hW
      (show 0 ≤ ((n+1:ℕ):ℝ)^(-eta/2) by positivity) hnX1 hnW2
      (native_comparison_thermal_intervalIntegrable (a n))
      (fun u hu=>(a n).actual_thermal_nonneg_on_unit hu)
    intro v hv hv2 hvlo hvupper
    have HD := hnDyad (a n) (hclock n) hnSmall hnW1 v hv hv2 hvlo hvupper
    have htarget : 0 < (a n).xs^4*v/
        (actualIntermediateMassEffectiveScale (a n).canonicalDirectTestBandScale v)^2 := by
      have hx := (a n).hxs
      have hB := actualIntermediateMassEffectiveScale_pos hW hv
      positivity
    have HI := (div_le_iff₀ htarget).mp HD
    simpa only [NativeOverlapContext.N,eta,mul_comm,neg_div] using HI

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
