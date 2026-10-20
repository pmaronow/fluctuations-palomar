module

public import ComparisonNativeActualRegularInitialMassMismatchAlong
public import ComparisonNativeActualSelectedBadHistoryReadout
public import ComparisonNativeActualHighMassSharpScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_initial_mismatch_clock_regularity
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (dim : ℕ→ℕ)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  filter_upwards [Hps] with n hn
  exact NativePullbackClockRegularity.of_shell_history
    (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
    (M n).alpha Temp epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl

theorem actual_selected_bad_history_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0) := by
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity dim root M
    epsilon shell hb hh Hhistory
  exact regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim Hclock C hC

theorem actual_selected_bad_history_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity dim root M
    epsilon shell hb hh Hhistory
  exact regular_minimum_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim Hclock C hC

theorem actual_selected_bad_history_original_retained_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*W n) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^3) atTop (𝓝 0) := by
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity dim root M
    epsilon shell hb hh Hhistory
  exact regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W v hxs hWlim Hclock C hC hv hvc

theorem actual_selected_bad_history_initial_mass_squared_mismatch_at_working_scale_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/((M n).xs)^3)
      atTop (𝓝 0) := by
  have Hxs:Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=
    squeeze_zero (fun n=>(M n).hxs.le)
      (fun n=>(M n).canonical_direct_test_band_ge_scale) hcanonical
  exact actual_selected_bad_history_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim root M (fun n=>(M n).xs)
    (fun _=>le_rfl) Hxs epsilon shell hb hh Hhistory C hC

theorem actual_selected_bad_history_original_retained_squared_mismatch_at_working_scale_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : ℕ→ℝ)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*(M n).xs) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/((M n).xs)^3) atTop (𝓝 0) := by
  have Hxs:Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=
    squeeze_zero (fun n=>(M n).hxs.le)
      (fun n=>(M n).canonical_direct_test_band_ge_scale) hcanonical
  exact actual_selected_bad_history_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim root M (fun n=>(M n).xs) v
    (fun _=>le_rfl) Hxs epsilon shell hb hh Hhistory C hC hv hvc

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
