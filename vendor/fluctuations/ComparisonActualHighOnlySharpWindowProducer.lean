module

public import ComparisonActualHighOnlySharpWindowPhysical
public import ComparisonSignedCavityActualSharpSlowWindowSequence

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 8000000
namespace ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum

theorem exists_actual_high_only_sharp_window_sequence_later_half
    {m delta cl cu Az C0 Ct D Bclock T L Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hT : 0 < T) (hL : 0 < L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
 :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n)) ∧
      ∀ᶠn : ℕ in atTop,(calibratedBandStart cu Az+2*L)*W n < (w n).star.val := by
  have hc1 := actualSlowWindowExponent_pos hm hdelta hroom
  have Hc1 := actualSlowWindowExponent_bounds hm hdelta
  obtain ⟨Cs,hCs,H⟩ := eventually_actual_high_only_sharp_slow_window_later_half
    hm hdelta hroom hcl hcu hAz hC0 hCt hCtest hT hL hc1 Hc1.1 Hc1.2.1
    dim hdim M G W hcanonical hWlim hcompare
  have Hex : ∀ᶠn : ℕ in atTop,
      ∃w : ActualSlowWindowChoice,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs w ∧
        (calibratedBandStart cu Az+2*L)*W n < w.star.val := by
    filter_upwards [H] with n hn
    obtain ⟨N,q,i,p,u,hi,hN,hq,hql,htotal,hnodes,hu,hH,hthermal,hlo,hhi,
      hrlo,hrhi,hxs,hz,hclock,hcomp,hosc,hsharp,hlate⟩ := hn
    exact ⟨⟨N,q,i,u⟩,⟨⟨p,hi,hN,hq,hql,htotal,hnodes,hu,hH,hthermal,hlo,hhi,
      hrlo,hrhi,hxs,hz,hclock,hcomp,hosc⟩,hsharp⟩,hlate⟩
  obtain ⟨w,hw⟩ := exists_point_sequence_of_eventually_exists
    (fun n w => IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs w ∧
      (calibratedBandStart cu Az+2*L)*W n < w.star.val) Hex
  exact ⟨Cs,hCs,w,hw.mono (fun _ h=>h.1),hw.mono (fun _ h=>h.2)⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
