module

public import ComparisonNativeActualSelectedBadHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N : ℕ→ℕ}

theorem actual_selected_bad_shell_history_near_bare_clocks
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hN : Tendsto N atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (epsilon shell : ℝ) (hshell : 0 < shell)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hxs : ∀ᶠn in atTop,(M n).xs ≤ W n) (hW : Tendsto W atTop (𝓝 0)) :
    ∀C eps : ℝ,0 ≤ C → 0 < eps → ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*W n),
      |(M n).b u-(T-epsilon)| ≤ eps*(W n)^2 ∧ |(M n).h u| ≤ eps*(W n)^3 := by
  have H:=actual_selected_bad_shell_history_sequential_clocks hm hdelta hcl hAz hC0 hc0 hc01
    hmargin hcapmargin hgapmargin hN epsilon shell hshell hb hh Hhistory
  have HW : ∀ᶠn in atTop,comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ W n := by
    filter_upwards [hxs] with n hn
    exact (M n).hscale.trans hn
  intro C eps hC heps
  have Hunit : ∀ᶠn in atTop,C*W n ≤ 1 := by
    have Hlim : Tendsto (fun n=>C*W n) atTop (𝓝 0) := by simpa only [mul_zero] using hW.const_mul C
    exact Hlim.eventually (eventually_le_nhds zero_lt_one)
  filter_upwards [H W hW HW C eps hC heps,Hunit] with n hn hnunit
  simpa only [min_eq_left hnunit] using hn

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
