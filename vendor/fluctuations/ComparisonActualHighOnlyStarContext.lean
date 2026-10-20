module

public import ComparisonActualHighOnlySharpWindowContext
public import ComparisonActualHighOnlyStarAllOrder
public import ComparisonActualHighOnlyStarFinalNet

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
theorem exists_actual_selected_bad_history_sharp_native_star_all_orders_comparable_context_high_only
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving := actualSlowWindowExponent m delta/64
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n)) ∧
      ∀p : ℕ,∃Craw : ℝ,0 < Craw ∧ ActualNativeStarOrderSavingAlong_high_only p Craw saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨Cs,hCs,w,hw⟩ := exists_actual_comparable_context_sharp_window_sequence_high_only
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hL dim hdim M G
    W hcanonical hWlim hcompare
  have hc := actualSlowWindowExponent_pos hm hdelta hroom
  have hw0 : ∀ᶠn in atTop,IsActualCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n) :=
    hw.mono fun _ h=>h.1
  refine ⟨by positivity,Cs,hCs,w,hw,?_⟩
  intro p
  exact eventually_actual_inherited_native_star_order_at_slow_window_along_high_only p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hCcal dim hdim M W hcanonical hWlim hcompare Cs hCs w hw0 (G.eventually_geometric_gates.mono fun n hn=>⟨hn.2,hn.1⟩)

theorem exists_actual_selected_bad_history_sharp_native_star_on_every_final_net_comparable_context_high_only
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving := actualSlowWindowExponent m delta/128
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n)) ∧
      (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong_high_only p saving M W w) ∧
      ∀A : ℕ,0 < A → ActualNativeStarFiniteDegreeOnEveryFinalNetAlong_high_only A saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,Cs,hCs,w,hw,H⟩ := exists_actual_selected_bad_history_sharp_native_star_all_orders_comparable_context_high_only (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim hcompare
  have hW n : 0 < W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_pos
  have Hfinal (p : ℕ) : ActualNativeStarMomentOnEveryFinalNetAlong_high_only p
      (actualSlowWindowExponent m delta/128) M W w := by
    obtain ⟨Craw,_,Horder⟩ := H p
    have HG := actual_native_star_order_saving_on_every_final_net_along_high_only p hs dim hdim M W hW w Horder
    simpa only [show (actualSlowWindowExponent m delta/64)/2=
      actualSlowWindowExponent m delta/128 by ring] using HG
  refine ⟨by linarith,Cs,hCs,w,hw,Hfinal,?_⟩
  intro A hA
  exact actual_native_star_final_net_to_finite_degrees_along_high_only A hA M W (fun n=>(hW n).le) w (Hfinal (A-1))

end OAI.SKFluctuations.LaplaceWindowFormalization
