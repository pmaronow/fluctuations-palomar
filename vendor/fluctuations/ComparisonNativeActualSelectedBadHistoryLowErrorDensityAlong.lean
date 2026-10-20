module

public import ComparisonNativeActualRegularLowErrorDensityAlong
public import ComparisonNativeActualSelectedBadHistoryReadout
public import ComparisonNativeActualShellHistoryThermalBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
set_option maxHeartbeats 14000000

theorem actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(M n).actualOriginalLowErrorDensitySaving C) atTop (𝓝 0) := by
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
    filter_upwards [Hps] with n hn
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha Temp epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
      (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl
  exact actualOriginalLowErrorDensitySaving_regular_tendsto_zero_along hm hdelta hroom hcl hcu hAz
    hC0 hCt hCompare dim hdim M hsmall hWlim Hclock C hC

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
