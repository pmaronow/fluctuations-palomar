module

public import ComparisonSignedCavitySecondLowActualHistoryFreshReplacementModulusAlong
public import ComparisonSignedCavitySecondLowFullCenteredB0ModulusAlong
public import ComparisonSignedCavitySecondLowFullCenteredB0AmplitudeAlong
public import ComparisonSignedCavitySecondLowActualStarOnlyB0AmplitudeAlong
public import SKProof.Port.ComparisonActualOriginalQLowDensitySourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 24000000
set_option autoImplicit false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
 def actualHistorySecondLowFreshReplacementAmplitude_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (eta Temp Cf Couter Cstar Csaved Cmoving : ℝ) : ℝ :=
  Cstar*((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))+
    Csaved*((n+1:ℕ):ℝ)^(-eta)+
    Cmoving*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
      (M.actualOriginalLowErrorDensitySaving (Couter+1)+(1/(n+1:ℕ):ℝ)/M.xs^2)

def actualSecondLowFullCenteredB0Amplitude_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (eta Temp Cf Couter Cstar Csaved Cmoving Crep : ℝ) : ℝ:=
  actualHistorySecondLowFreshReplacementAmplitude_original_q M eta Temp Cf Couter Cstar Csaved Cmoving+
    Crep*(n:ℝ)^(-eta)

theorem actual_second_low_full_centered_B0_amplitude_nonneg_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (eta Temp Cf Couter Cstar Csaved Cmoving Crep : ℝ)
    (hTemp : 0≤Temp) (hCouter : 0≤Couter) (hCstar : 0≤Cstar) (hCsaved : 0≤Csaved)
    (hCmoving : 0≤Cmoving) (hCrep : 0≤Crep) :
    0≤actualSecondLowFullCenteredB0Amplitude_original_q M eta Temp Cf Couter Cstar Csaved Cmoving Crep := by
  have HD:0 < M.actualOriginalLowErrorDensitySaving (Couter+1):=
    M.actualOriginalLowErrorDensitySaving_pos (by linarith)
  have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
  dsimp [actualSecondLowFullCenteredB0Amplitude_original_q,actualHistorySecondLowFreshReplacementAmplitude_original_q]
  positivity

theorem actual_second_low_star_only_full_B0_amplitude_regular_tendsto_zero_along_original_q
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Couter Cstar Cmoving Crep Ccompare : ℝ}
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare) (hCouter : 0 ≤ Couter)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).directTestWorkingScale) atTop (𝓝 0))
    (Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs) :
    Tendsto (fun n=>actualSecondLowFullCenteredB0Amplitude_original_q (M n)
      eta Temp Cf Couter Cstar 0 Cmoving Crep) atTop (𝓝 0) := by
  have HD:=actualOriginalLowErrorDensitySaving_regular_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M hsmall hWlim Hclock Homit Hcutoff
    (Couter+1) (by linarith)
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along_original_q hm hC0 dim hdim M
  have Hstar:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
    (by norm_num : (0:ℝ)<32))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have HR:=classified_dyadic_fold_saving_amplitude_tendsto_zero_along Crep eta heta dim hdim
  have H:=((Hstar.const_mul Cstar).add
    ((HD.add HI).const_mul (Cmoving*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp))).add HR
  simpa only [actualSecondLowFullCenteredB0Amplitude_original_q,actualHistorySecondLowFreshReplacementAmplitude_original_q,
    Function.comp_def,zero_mul,mul_zero,add_zero] using H

end OAI.SKFluctuations.Cavity
