module

public import ComparisonSignedCavityActualInheritedLowErrorDensity
public import ComparisonSignedCavityActualLowErrorSavingAlong
public import ComparisonNativeActualRegularLowErrorDensityAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem actualMinimumInheritedLowErrorDensityAmplitude_regular_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>actualMinimumInheritedLowErrorDensityAmplitude (M n) Temp Cf C) atTop (𝓝 0) := by
  have HS:=NativeOverlapMinimum.actualOriginalLowErrorDensitySaving_regular_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M hsmall hWlim hclock C hC
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along hm hC0 dim hdim M
  have H:=(HS.add HI).const_mul (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp)
  simpa only [actualMinimumInheritedLowErrorDensityAmplitude,add_zero,mul_zero] using H

end OAI.SKFluctuations.Cavity
