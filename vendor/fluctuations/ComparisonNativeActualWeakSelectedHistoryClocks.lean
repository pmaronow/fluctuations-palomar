module

public import ComparisonNativeActualChildSequentialClocksGeneral
public import ComparisonNativeActualSelectedBadHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N : ℕ→ℕ}

inductive ActualWeakSelectedHistoryChain (c0 : ℝ)
    (root : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock) :
    ((n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)→Prop
  | root : ActualWeakSelectedHistoryChain c0 root root
  | child {P M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
      (history : ActualWeakSelectedHistoryChain c0 root P)
      (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
      (htarget : ∀ᶠn in atTop,
        comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam ≤ x n)
      (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
      (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
        atTop (𝓝 0))
      (hd : ∀ᶠn in atTop,(M n).context.d=actualChildRadius c0 (x n))
      (hE : ∀ᶠn in atTop,(M n).context.E=actualChildErrorBudget (N n+1) delta c0 (P n).context.d (P n).lam (x n))
      (hb : ∀ᶠn in atTop,∀u,(M n).b u=(P n).b u-laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u))
      (hh : ∀ᶠn in atTop,∀u,(M n).h u=(P n).h u+laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u) :
      ActualWeakSelectedHistoryChain c0 root M

theorem ActualWeakSelectedHistoryChain.sequential_clocks
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hN : Tendsto N atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hroot : NativeSequentialPositiveBandClocks root T)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) : NativeSequentialPositiveBandClocks M T := by
  induction Hhistory with
  | root=>exact Hroot
  | @child P M history x hx hxunit htarget hcap hweak hd hE hb hh ih=>
    exact actual_selected_bad_child_sequential_clocks_of_call_bounded hm hdelta hcl hAz hC0 hc0 hc01
      hmargin hcapmargin hgapmargin hN P M x hx hxunit htarget hcap hweak hd hE hb hh ih

theorem actual_weak_selected_bad_shell_history_sequential_clocks
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hN : Tendsto N atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (epsilon shell : ℝ) (hshell : 0 < shell)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) :
    NativeSequentialPositiveBandClocks M (T-epsilon) :=
  Hhistory.sequential_clocks hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hN
    (actual_initial_shell_sequential_clocks root epsilon shell hshell hb hh)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
