module

public import ComparisonSignedCavityActualHistorySharpWindowSequence
public import ComparisonNativeInheritedStarActualFinalNet

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer NativeOverlapMinimum

theorem exists_actual_selected_bad_history_sharp_native_star_all_orders
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
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
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving := actualSlowWindowExponent m delta/64
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
      ∀p : ℕ,∃Craw : ℝ,0 < Craw ∧ ActualNativeStarOrderSavingAlong p Craw saving M W w := by
  obtain ⟨Cs,hCs,w,hw⟩ := exists_actual_selected_bad_history_sharp_window_sequence
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hL hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hshell hTemp hb hh Hhistory
    W hcanonical hWlim hcompare
  have hc := actualSlowWindowExponent_pos hm hdelta hroom
  have hw0 : ∀ᶠn in atTop,IsActualCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n) :=
    hw.mono fun _ h=>h.1
  refine ⟨by positivity,Cs,hCs,w,hw,?_⟩
  intro p
  exact eventually_actual_inherited_native_star_order_at_slow_window_along p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hCcal dim hdim M W hcanonical hWlim hcompare Cs hCs w hw0

theorem exists_actual_selected_bad_history_sharp_native_star_on_every_final_net
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
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
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving := actualSlowWindowExponent m delta/128
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
      (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      ∀A : ℕ,0 < A → ActualNativeStarFiniteDegreeOnEveryFinalNetAlong A saving M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,H⟩ := exists_actual_selected_bad_history_sharp_native_star_all_orders
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hW n : 0 < W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_pos
  have Hfinal (p : ℕ) : ActualNativeStarMomentOnEveryFinalNetAlong p
      (actualSlowWindowExponent m delta/128) M W w := by
    obtain ⟨Craw,_,Horder⟩ := H p
    have HG := actual_native_star_order_saving_on_every_final_net_along p hs dim hdim M W hW w Horder
    simpa only [show (actualSlowWindowExponent m delta/64)/2=
      actualSlowWindowExponent m delta/128 by ring] using HG
  refine ⟨by linarith,Cs,hCs,w,hw,Hfinal,?_⟩
  intro A hA
  exact actual_native_star_final_net_to_finite_degrees_along A hA M W (fun n=>(hW n).le) w (Hfinal (A-1))

end OAI.SKFluctuations.LaplaceWindowFormalization
