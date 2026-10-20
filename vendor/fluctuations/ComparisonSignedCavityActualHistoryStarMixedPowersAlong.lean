module

public import ComparisonSignedCavityActualHistorySharpStarAllOrder
public import ComparisonNativeActualSelectedBadHistorySourceClocks
public import ComparisonSignedCavityActualInheritedProjectionPowersAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 14000000

theorem exists_actual_selected_bad_history_sharp_star_all_mixed_projection_powers_along
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
        (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong p
          (actualSlowWindowExponent m delta/128) M W w) ∧
        (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p saving M W w) ∧
        ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon (by linarith : 0 ≤ T) hb hh Hhistory
  obtain ⟨hs,Cs,hCs,w,hw,HnativeAlong,_⟩:=
    exists_actual_selected_bad_history_sharp_native_star_on_every_final_net
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have Hnative (p : ℕ) : ActualNativeStarMomentOnEveryFinalNetAlong p
      (actualSlowWindowExponent m delta/128) M W w := HnativeAlong p
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hsite : actualSlowWindowExponent m delta/128 < (5:ℝ)/6+m := by
    have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
    linarith
  have HG:=actual_inherited_native_star_to_all_projection_powers_along hCf hC0 hs hsite
    dim hdim M W hxs hWlim Hsource w Hnative
  refine ⟨by linarith,Cf,hCf,Hsource,Cs,hCs,w,hw,Hnative,?_⟩
  simpa only [show (actualSlowWindowExponent m delta/128)/2=
    actualSlowWindowExponent m delta/256 by ring] using HG

end OAI.SKFluctuations.LaplaceWindowFormalization
