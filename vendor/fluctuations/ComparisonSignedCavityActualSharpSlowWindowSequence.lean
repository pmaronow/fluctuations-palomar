module

public import ComparisonSignedCavityActualSharpSlowWindowStar

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum

def IsActualSharpCalibratedSlowWindow
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W T L Cs : ℝ) (w : ActualSlowWindowChoice) : Prop :=
  IsActualCalibratedSlowWindow M W T L Cs w ∧
    orderedPathB (n+1) M.bf M.hf w.star.val-
      (orderedPathS (n+1) M.bf M.hf w.star.val)^2 ≤
      M.context.N^(-(actualMassSavingExponent m delta/4))*(M.xs^4/W^2)

theorem exists_actual_bare_sharp_calibrated_slow_window_sequence
    {m delta cl cu Az C0 Ct D Bclock T L Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hT : 0 < T) (hL : 0 < L)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ → ActualSlowWindowChoice,
      ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n) := by
  have hc1 := actualSlowWindowExponent_pos hm hdelta hroom
  have Hc1 := actualSlowWindowExponent_bounds hm hdelta
  obtain ⟨Cs,hCs,H⟩ := eventually_actual_bare_sharp_calibrated_slow_window
    hm hdelta hroom hcl hcu hAz hC0 hCt hCtest hT hL hc1 Hc1.1 Hc1.2.1
    M W hcanonical hWlim hcompare hb hh
  have Hex : ∀ᶠn : ℕ in atTop,
      ∃w : ActualSlowWindowChoice,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs w := by
    filter_upwards [H] with n hn
    obtain ⟨N,q,i,p,u,hi,hN,hq,hql,htotal,hnodes,hu,hH,hthermal,hlo,hhi,
      hrlo,hrhi,hxs,hz,hclock,hcomp,hosc,hsharp⟩ := hn
    exact ⟨⟨N,q,i,u⟩,⟨p,hi,hN,hq,hql,htotal,hnodes,hu,hH,hthermal,hlo,hhi,
      hrlo,hrhi,hxs,hz,hclock,hcomp,hosc⟩,hsharp⟩
  obtain ⟨w,hw⟩ := exists_point_sequence_of_eventually_exists
    (fun n w => IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs w) Hex
  exact ⟨Cs,hCs,w,hw⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
