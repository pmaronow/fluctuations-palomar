module

public import ComparisonSignedCavitySecondLowOriginalConstantB0Vanishing
public import ComparisonSignedCavityActualLowErrorSavingAlong
public import ComparisonNativeActualSelectedBadHistoryLowErrorDensityAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 14000000

theorem actual_second_low_inherited_constant_B0_amplitude_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Couter C Ccompare c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare) (hCouter : 0 ≤ Couter)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    Tendsto (fun n=>actualSecondLowOriginalConstantB0Amplitude (M n) Temp Cf Couter C)
      atTop (𝓝 0) := by
  have HS:=actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim root M epsilon shell hb hh Hhistory
    hsmall hWlim (Couter+1) (by linarith)
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along hm hC0 dim hdim M
  have heta : 0 < actualMassSavingExponent m delta/32 :=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have HP:=(tendsto_rpow_neg_atTop heta).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have H:=HP.const_mul 16 |>.add
    ((HS.add HI).const_mul (C*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp))
  simpa only [actualSecondLowOriginalConstantB0Amplitude,Function.comp_def,add_zero,mul_zero] using H

end OAI.SKFluctuations.Cavity
