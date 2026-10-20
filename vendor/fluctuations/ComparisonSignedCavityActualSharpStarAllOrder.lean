module

public import ComparisonSignedCavityActualSharpSlowWindowSequence
public import ComparisonNativeStarActualFinalNet

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer NativeOverlapMinimum

theorem exists_actual_bare_sharp_native_star_all_orders
    {m delta cl cu Az C0 Ct D Bclock T L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    let saving := actualSlowWindowExponent m delta/64
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      ∀p : ℕ,∃Craw : ℝ,0 < Craw ∧ ActualNativeStarOrderSaving p Craw saving M W w := by
  obtain ⟨Cs,hCs,w,hw⟩ := exists_actual_bare_sharp_calibrated_slow_window_sequence
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hT hL
    M W hcanonical hWlim hcompare hb hh
  have hc := actualSlowWindowExponent_pos hm hdelta hroom
  have hw0 : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n) :=
    hw.mono fun _ h=>h.1
  refine ⟨by positivity,Cs,hCs,w,hw,?_⟩
  intro p
  exact eventually_actual_bare_native_star_order_at_slow_window p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hCcal M W hcanonical hWlim hcompare hh Cs hCs w hw0

theorem exists_actual_bare_sharp_native_star_on_every_final_net
    {m delta cl cu Az C0 Ct D Bclock T L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    let saving := actualSlowWindowExponent m delta/128
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNet p saving M W w) ∧
      ∀A : ℕ,0 < A → ActualNativeStarFiniteDegreeOnEveryFinalNet A saving M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,H⟩ := exists_actual_bare_sharp_native_star_all_orders
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL hCcal M W hcanonical hWlim hcompare hb hh
  have hW n : 0 < W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_pos
  have Hfinal (p : ℕ) : ActualNativeStarMomentOnEveryFinalNet p
      (actualSlowWindowExponent m delta/128) M W w := by
    obtain ⟨Craw,_,Horder⟩ := H p
    have HG := actual_native_star_order_saving_on_every_final_net p hs M W hW w Horder
    simpa only [show (actualSlowWindowExponent m delta/64)/2=
      actualSlowWindowExponent m delta/128 by ring] using HG
  refine ⟨by linarith,Cs,hCs,w,hw,Hfinal,?_⟩
  intro A hA
  exact actual_native_star_final_net_to_finite_degrees A hA M W (fun n=>(hW n).le) w (Hfinal (A-1))

end OAI.SKFluctuations.LaplaceWindowFormalization
