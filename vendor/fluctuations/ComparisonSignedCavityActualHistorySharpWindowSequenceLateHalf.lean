module

public import ComparisonSignedCavityActualRegularSharpWindowSequenceLateHalf
public import ComparisonNativeActualHistoryNearBareClocks
public import ComparisonNativeActualSelectedBadHistoryReadout

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum

theorem exists_actual_selected_bad_history_sharp_window_sequence_later_half
    {m delta cl cu Az C0 Ct D Bclock T L Ctest c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
      ∀ᶠn in atTop,(calibratedBandStart cu Az+2*L)*W n < (w n).star.val := by
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks hm hdelta hcl hAz hC0 hc0 hc01
    hmargin hcapmargin hgapmargin hdim epsilon shell hshell hb hh Hhistory W
    (Eventually.of_forall hxs) hWlim
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
    filter_upwards [Hps] with n hn
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha T epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
      (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl
  exact exists_actual_regular_near_bare_sharp_window_sequence_later_half hm hdelta hroom hcl hcu hAz hC0 hCt
    hCtest hTemp hL dim hdim M W hcanonical hWlim hcompare Hclock Hnear

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
