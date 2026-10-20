module

public import ComparisonNativeActualLowerShellHistoryClocks
public import ComparisonNativeActualGeneralHistoryContext
public import ComparisonNativeActualHistoryWeakenConstants

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock cl' cu' Az' Ct' D' Bclock' c0 T : ℝ} {dim : ℕ→ℕ}

theorem ActualWeakSelectedHistoryChain.weaken_constants
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    ActualWeakSelectedHistoryChain c0
      (fun n=>(root n).weakenConstants hcl hcu hAz hCt hD hB)
      (fun n=>(M n).weakenConstants hcl hcu hAz hCt hD hB) := by
  induction Hhistory with
  | root => exact .root
  | @child P M history x hx hxunit htarget hcap hweak hd hE hb hh ih =>
    apply ActualWeakSelectedHistoryChain.child ih x hx hxunit htarget ?_ hweak hd hE hb hh
    filter_upwards [hcap] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right hAz (hx n).le)

def ActualNativeProfileHistory.weaken_constants
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : ActualNativeProfileHistory M T c0)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    ActualNativeProfileHistory (fun n=>(M n).weakenConstants hcl hcu hAz hCt hD hB) T c0 where
  root := fun n=>(G.root n).weakenConstants hcl hcu hAz hCt hD hB
  epsilon := G.epsilon
  shell := G.shell
  hepsilon := G.hepsilon
  hb := G.hb
  hh := G.hh
  history := G.history.weaken_constants hcl hcu hAz hCt hD hB
  sequential := G.sequential
  xs_zero := G.xs_zero
  hT := G.hT

def ActualNativeProfileHistory.append_child
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    {P : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : ActualNativeProfileHistory P T c0)
    (Q : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hd : ∀ᶠn in atTop,(Q n).context.d=actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop,(Q n).context.E=actualChildErrorBudget (dim n+1) delta c0
      (P n).context.d (P n).lam (x n))
    (hb : ∀ᶠn in atTop,∀u,(Q n).b u=(P n).b u-
      laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u))
    (hh : ∀ᶠn in atTop,∀u,(Q n).h u=(P n).h u+
      laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u)
    (hQxs : Tendsto (fun n=>(Q n).xs) atTop (𝓝 0)) :
    ActualNativeProfileHistory Q T c0 where
  root := G.root
  epsilon := G.epsilon
  shell := G.shell
  hepsilon := G.hepsilon
  hb := G.hb
  hh := G.hh
  history := .child G.history x hx hxunit htarget hcap hweak hd hE hb hh
  sequential := actual_selected_bad_child_sequential_clocks_of_call_bounded hm hdelta hcl hAz hC0
    hc0 hc01 hmargin hcapmargin hgapmargin hdim P Q x hx hxunit htarget hcap hweak hd hE hb hh G.sequential
  xs_zero := hQxs
  hT := G.hT

def actual_lower_shell_profile_history
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hT : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (shell : ℕ→ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=
      initialShellMatrixClock T (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ActualNativeProfileHistory M T c0 where
  root := root
  epsilon := fun n=>((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)
  shell := shell
  hepsilon := fun n=>Real.rpow_nonneg (root n).context.hN.le _
  hb := hb
  hh := hh
  history := Hhistory
  sequential := (actual_weak_lower_shell_history_clock_data hm hdelta hcl hAz hC0 hc0 hc01 hT.le
    hmargin hcapmargin hgapmargin dim hdim root M shell hb hh Hhistory).1
  xs_zero := hxs
  hT := hT

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
