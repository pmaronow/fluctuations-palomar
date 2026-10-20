module

public import ComparisonSignedCavitySecondLowFullCenteredB0ModulusAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum

theorem actual_second_low_full_centered_B0_amplitude_nonneg
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (eta Temp Cf Couter Cstar Csaved Cmoving Crep : ℝ)
    (hTemp : 0≤Temp) (hCouter : 0≤Couter) (hCstar : 0≤Cstar) (hCsaved : 0≤Csaved)
    (hCmoving : 0≤Cmoving) (hCrep : 0≤Crep) :
    0≤actualSecondLowFullCenteredB0Amplitude M eta Temp Cf Couter Cstar Csaved Cmoving Crep := by
  have HD:0 < M.actualOriginalLowErrorDensitySaving (Couter+1):=
    M.actualOriginalLowErrorDensitySaving_pos (by linarith)
  have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
  dsimp [actualSecondLowFullCenteredB0Amplitude,actualHistorySecondLowFreshReplacementAmplitude]
  positivity

theorem actual_second_low_full_centered_B0_amplitude_tendsto_zero_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Couter Cstar Csaved Cmoving Crep Ccompare c0 : ℝ}
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCompare : 0≤Ccompare) (hCouter : 0≤Couter)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    Tendsto (fun n=>actualSecondLowFullCenteredB0Amplitude (M n)
      eta Temp Cf Couter Cstar Csaved Cmoving Crep) atTop (𝓝 0) := by
  have HA:=actual_history_second_low_fresh_replacement_amplitude_tendsto_zero_along
    heta hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hCouter dim hdim root M
    epsilon shell hb hh Hhistory hsmall hWlim
    (Temp:=Temp) (Cf:=Cf) (Cstar:=Cstar) (Csaved:=Csaved) (Cmoving:=Cmoving)
  have HR:=classified_dyadic_fold_saving_amplitude_tendsto_zero_along Crep eta heta dim hdim
  simpa only [actualSecondLowFullCenteredB0Amplitude,add_zero] using HA.add HR

end OAI.SKFluctuations.Cavity
