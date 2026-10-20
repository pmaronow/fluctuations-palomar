module

public import ComparisonSignedCavityActualHistoryFreshPairFeedbackAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_all_mixed_projection_powers_at_sharp_window_along
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (_hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (_hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (_hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
        (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong p
          (actualSlowWindowExponent m delta/128) M W w) ∧
        (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p saving M W w) ∧
        ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon (by linarith : 0 ≤ T) hb hh Hhistory
  have hc := actualSlowWindowExponent_pos hm hdelta hroom
  have hs : 0 < actualSlowWindowExponent m delta/128 := by positivity
  have hW n : 0 < W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_pos
  have Hnative (p : ℕ) : ActualNativeStarMomentOnEveryFinalNetAlong p
      (actualSlowWindowExponent m delta/128) M W w := by
    obtain ⟨Craw,_,Horder⟩ := eventually_actual_inherited_native_star_order_at_slow_window_along p
      hm hdelta hroom hcl hcu hAz hC0 hCt hL hCcal dim hdim M W hcanonical hWlim hcompare
      Cs hCs w (hw.mono (fun _ hn=>hn.1))
    have HG := actual_native_star_order_saving_on_every_final_net_along p
      (by positivity : 0 < actualSlowWindowExponent m delta/64) dim hdim M W hW w Horder
    simpa only [show (actualSlowWindowExponent m delta/64)/2=
      actualSlowWindowExponent m delta/128 by ring] using HG
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hsite : actualSlowWindowExponent m delta/128 < (5:ℝ)/6+m := by
    have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
    linarith
  have HG:=actual_inherited_native_star_to_all_projection_powers_along hCf hC0 hs hsite
    dim hdim M W hxs hWlim Hsource w Hnative
  refine ⟨by linarith,Cf,hCf,Hsource,hw,Hnative,?_⟩
  simpa only [show (actualSlowWindowExponent m delta/128)/2=
    actualSlowWindowExponent m delta/256 by ring] using HG

theorem actual_selected_bad_history_square_resource_pair_budgets_at_sharp_window_along
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
        (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
        ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
          (actualMassSavingExponent m delta/32) M W w ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
          ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong
            degree A saving Cmass M W w) ∧
        ∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w := by
  obtain ⟨hs,Cf,hCf,Hsource,hw,Hnative,_,_,Hmixed⟩:=
    actual_selected_bad_history_all_mixed_projection_powers_at_sharp_window_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare Cs hCs w hw
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hsite : actualSlowWindowExponent m delta/128 < (5:ℝ)/6+m := by
    have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
    linarith
  have Hsquare (p : ℕ) : ActualOriginalSquareStarMomentOnEveryFinalNetAlong p
      (actualSlowWindowExponent m delta/256) M W w := by
    have HG:=actual_inherited_native_star_every_final_net_to_square_along p hCf hC0
      (by linarith : 0 < actualSlowWindowExponent m delta/128) hsite dim hdim M W hxs hWlim Hsource w (Hnative p)
    simpa only [show (actualSlowWindowExponent m delta/128)/2=
      actualSlowWindowExponent m delta/256 by ring] using HG
  have Hsharp:=eventually_actual_sharp_star_inherited_endpoint_second_along
    hm hdelta hC0 hCf dim hdim M W hcanonical hWlim w Hsource hw
  refine ⟨hs,Cf,hCf,Hsource,hw,Hsquare,Hmixed,Hsharp,?_,?_⟩
  · intro Cmass hCm degree hd
    exact actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along degree hd
      hm hdelta hroom hcl hcu hAz hC0 hCt (by linarith : 0 ≤ T) hCf Cmass hCm
      dim hdim M W hxs hWlim Hsource w (Hsquare (degree-1))
  · intro degree hd
    exact actual_square_constant_resource_pair_budget_of_actual_star_producer_along degree hd
      M W hxs w (Hsquare (degree-1))

theorem actual_selected_bad_history_sharp_fresh_pair_feedback_at_sharp_window_along
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0 < saving ∧ 0 < sharpSaving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
        (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
        ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong sharpSaving M W w ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
          ∃A : ℝ,1 ≤ A ∧
            ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w ∧
            ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong
              degree A saving sharpSaving Cmass M W w) ∧
        ∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w ∧
          ActualOriginalConstantFreshPairSavingOnEveryFinalNetAlong degree saving sharpSaving M W w := by
  obtain ⟨hs,Cf,hCf,Hsource,hw,Hsquare,Hmixed,Hsharp,Hpair,Hconstant⟩:=
    actual_selected_bad_history_square_resource_pair_budgets_at_sharp_window_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare Cs hCs w hw
  have hsharp : 0 < actualMassSavingExponent m delta/32 :=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨hs,hsharp,Cf,hCf,Hsource,hw,Hsquare,Hmixed,Hsharp,?_,?_⟩
  · intro Cmass hCm degree hd
    obtain ⟨A,hA,HA⟩:=Hpair Cmass hCm degree hd
    exact ⟨A,hA,HA,actual_fresh_pair_resource_saving_from_genuine_pair_and_sharp_star_along
      degree A hA M W hxs w HA Hsharp⟩
  · intro degree hd
    exact ⟨Hconstant degree hd,
      actual_constant_fresh_pair_saving_from_genuine_pair_and_sharp_star_along
        degree M W hxs w (Hconstant degree hd) Hsharp⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
