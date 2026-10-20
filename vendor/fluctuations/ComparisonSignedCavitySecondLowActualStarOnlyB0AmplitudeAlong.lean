module

public import ComparisonSignedCavitySecondLowFullCenteredB0AmplitudeAlong
public import ComparisonSignedCavityActualInheritedLowErrorDensityAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000

theorem actual_second_low_star_only_full_B0_amplitude_regular_tendsto_zero_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Couter Cstar Cmoving Crep Ccompare : ℝ}
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare) (hCouter : 0 ≤ Couter)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1) :
    Tendsto (fun n=>actualSecondLowFullCenteredB0Amplitude (M n)
      eta Temp Cf Couter Cstar 0 Cmoving Crep) atTop (𝓝 0) := by
  have HD:=actualOriginalLowErrorDensitySaving_regular_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M hsmall hWlim Hclock
    (Couter+1) (by linarith)
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along hm hC0 dim hdim M
  have Hstar:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
    (by norm_num : (0:ℝ)<32))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have HR:=classified_dyadic_fold_saving_amplitude_tendsto_zero_along Crep eta heta dim hdim
  have H:=((Hstar.const_mul Cstar).add
    ((HD.add HI).const_mul (Cmoving*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp))).add HR
  simpa only [actualSecondLowFullCenteredB0Amplitude,actualHistorySecondLowFreshReplacementAmplitude,
    Function.comp_def,zero_mul,mul_zero,add_zero] using H

end OAI.SKFluctuations.Cavity
