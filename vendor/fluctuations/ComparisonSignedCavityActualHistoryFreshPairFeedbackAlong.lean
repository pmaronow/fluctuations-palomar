module

public import ComparisonSignedCavityActualFreshPairEndpointMomentAlong
public import ComparisonSignedCavityActualConstantFreshPairFeedbackAlong
public import ComparisonSignedCavityActualHistorySquareResourceAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 18000000

theorem exists_actual_selected_bad_history_sharp_fresh_pair_feedback_along
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
    let sharpSaving:=actualMassSavingExponent m delta/32
    0 < saving ∧ 0 < sharpSaving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
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
  obtain ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,Hpair,Hconstant⟩:=
    exists_actual_selected_bad_history_square_resource_pair_budgets_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hsharp : 0 < actualMassSavingExponent m delta/32 :=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨hs,hsharp,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,?_,?_⟩
  · intro Cmass hCm degree hd
    obtain ⟨A,hA,HA⟩:=Hpair Cmass hCm degree hd
    exact ⟨A,hA,HA,actual_fresh_pair_resource_saving_from_genuine_pair_and_sharp_star_along
      degree A hA M W hxs w HA Hsharp⟩
  · intro degree hd
    exact ⟨Hconstant degree hd,
      actual_constant_fresh_pair_saving_from_genuine_pair_and_sharp_star_along
        degree M W hxs w (Hconstant degree hd) Hsharp⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
