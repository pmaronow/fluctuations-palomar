module

public import ComparisonSignedCavityActualHistoryStarMixedPowersAlong
public import ComparisonSignedCavityActualSquareConstantPairAlong
public import ComparisonSignedCavitySharpEndpointSecondAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem exists_actual_selected_bad_history_square_resource_pair_budgets_along
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
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
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
  obtain ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hnative,_,_,Hmixed⟩:=
    exists_actual_selected_bad_history_sharp_star_all_mixed_projection_powers_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
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
  refine ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,?_,?_⟩
  · intro Cmass hCm degree hd
    exact actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along degree hd
      hm hdelta hroom hcl hcu hAz hC0 hCt (by linarith : 0 ≤ T) hCf Cmass hCm
      dim hdim M W hxs hWlim Hsource w (Hsquare (degree-1))
  · intro degree hd
    exact actual_square_constant_resource_pair_budget_of_actual_star_producer_along degree hd
      M W hxs w (Hsquare (degree-1))

end OAI.SKFluctuations.LaplaceWindowFormalization
