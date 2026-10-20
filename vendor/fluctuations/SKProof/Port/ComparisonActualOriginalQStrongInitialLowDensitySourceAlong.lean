module

public import ComparisonNativeMassDyadicThermalBand
public import SKProof.Port.ComparisonActualOriginalQStrongIntermediateMassPhysicalDyad
public import SKProof.Port.ComparisonActualOriginalQRegularInitialMassErrorAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
namespace ActualThetaZeroOverlapMinimum
theorem regular_minimum_strong_initial_mass_error_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).data.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).directTestWorkingScale) atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (a n).alpha.val.val (a n).b (a n).h (a n).data.rmin 1)
    (Homit : Tendsto (fun n=>(a n).data.s/(a n).xs) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(a n).data.s≤1/4 ∧ (a n).data.s≤(a n).xs)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>
      (∫u in 0..min (C*(a n).directTestWorkingScale) 1,
        Real.sqrt (orderedPathB (dim n+1) (a n).sweepBf (a n).sweepHf u-
          (orderedPathS (dim n+1) (a n).sweepBf (a n).sweepHf u)^2))/(a n).xs^2)
      atTop (𝓝 0) := by
  let c := 2*cu*(Az+1)+1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcouter : 2*cu*(Az+1) ≤ c := by dsimp [c]; linarith
  have HX : Tendsto (fun n=>(a n).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(a n).hxs.le)
      (fun n=>(a n).canonical_direct_test_band_ge_scale) hWlim
  have Hinitial := regular_minimum_initial_mass_error_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim a (fun n=>(a n).xs)
    (fun _=>le_rfl) HX hclock Homit Hcutoff c hc
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hdyad := hdim.eventually (eventually_actual_regular_strong_intermediate_mass_dyad_original_q
    (D:=D) (Cs:=Cs) C Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter)
  have HOmit64:=Homit.eventually (eventually_le_nhds (show (0:ℝ) < c/64 by positivity))
  have Hpow : Tendsto (fun n : ℕ=>((dim n+1:ℕ):ℝ)^(-eta/2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (half_pos heta)).comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
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
  · filter_upwards [Hdyad,hsmall,HW1,HW2,HX1,hclock,Hcutoff,HOmit64] with n hnDyad hnSmall hnW1 hnW2 hnX1 hnclock hnCut hnOmit
    have hW := (a n).canonical_direct_test_band_pos
    have htop : C*(a n).directTestWorkingScale ≤ 1 := by
      nlinarith [mul_pos hC hW]
    rw [min_eq_left htop]
    apply native_initial_plus_intermediate_error_ratio_le hc hC (a n).hxs hW
      (show 0 ≤ ((dim n+1:ℕ):ℝ)^(-eta/2) by positivity) hnX1 hnW2
      ((a n).original_thermal_intervalIntegrable)
      (fun u hu=>(a n).actual_thermal_nonneg_on_unit hu)
    intro v hv hv2 hvlo hvupper
    have Hs64 : 64*(a n).data.s ≤ c*(a n).xs:=by
      have H:= (div_le_iff₀ (a n).hxs).mp hnOmit
      linarith only [H]
    have HD := hnDyad (a n) hnclock hnCut.1 hnCut.2 Hs64 hnSmall hnW1 v hv hv2 hvlo hvupper
    have htarget : 0 < (a n).xs^4*v/
        (actualIntermediateMassEffectiveScale (a n).directTestWorkingScale v)^2 := by
      have hx := (a n).hxs
      have hB := actualIntermediateMassEffectiveScale_pos hW hv
      positivity
    have HI := (div_le_iff₀ htarget).mp HD
    simpa only [ActualHighWallData.N,eta,mul_comm,neg_div] using HI

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
