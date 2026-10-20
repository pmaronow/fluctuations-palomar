module

public import ComparisonSignedCavityActualTargetInitialResidualAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 5000000

theorem exists_actual_selected_bad_history_initial_residual_approx_along
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
        (∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
        ∀Cmass : ℝ,0 ≤ Cmass →∃threshold : ℕ,0 < threshold ∧∃savingR : ℝ,0 < savingR ∧
          ∀depth : ℕ,threshold ≤ depth →
            ActualTargetInitialResidualApproxAlong depth savingR Cmass M W w := by
  obtain ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,Hp,Hconstant⟩:=
    exists_actual_selected_bad_history_square_resource_pair_budgets_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Htotal:=actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  refine ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,Hp,Hconstant,?_⟩
  intro Cmass hCm
  exact exists_actual_same_star_initial_residual_approx_along
    hm hcu hAz hC0 (by linarith : 0≤T) hTemp hs Cmass dim hdim M W hxs hWlim
    (Htotal.mono fun _ h=>h.1) (Htotal.mono fun _ h=>h.2) w hw (Hp Cmass hCm)

end OAI.SKFluctuations.LaplaceWindowFormalization
