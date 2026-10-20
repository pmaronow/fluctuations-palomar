module

public import ComparisonSignedCavityActualSharpSlowWindowSequence

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 7000000

namespace NativeOverlapMinimum

theorem eventually_actual_bare_native_clock_at_slow_window
    {m delta cl cu Az C0 Ct D Bclock T L : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hT : 0 < T)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0)
    (Cs : ℝ) (w : ℕ → ActualSlowWindowChoice)
    (Hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    ∀ᶠn : ℕ in atTop,
      let c := starMassBandConstant cu Az/cu
      let B := 2*bareSourceClockConstant cl Az D+T
      ∀us : List PositiveMass,(∀v∈us,v.val ≤ 1) → (w n).star ∈ us →
      ∀ᶠk : ℕ in atTop,
        let as := finiteCutMasses us k
        let u := (w n).star.val
        let K := retainedStarMixedClock n (M n).bf (M n).hf as
        (3*T*c/16)*W n ≤ K (retainedMassPrefixIndex u as) ∧
        |K (retainedMassPrefixIndex u as)-T*orderedPathS (n+1) (M n).bf (M n).hf u| ≤
          ((c+1)/4+1)*(W n)^3 ∧
        ∀(tree : ClockTree (Spin n×Bool) as) (start : ℝ)
          (_hoa : MassOrdered start as) (U : ℕ) (_hU0 : 0 < U) (_hU : U ≤ as.length)
          (s : tree.Slot) (beta Cbeta : ℝ),|beta| ≤ Cbeta →
        let chi := ((tree.markedAttach start).map (fun p => p.coeff*
          fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
        |beta/(chi*K (retainedMassPrefixIndex u as))| ≤
          Cbeta/(Real.exp (-4*B)*(3*T*c/16)*W n) := by
  have HW1 := hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [Hw,HW1] with n hn hnW1
  dsimp only
  intro us hus hstar
  let c := starMassBandConstant cu Az/cu
  let B := 2*bareSourceClockConstant cl Az D+T
  have hc : 0 < c := div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hK,hcomp,_⟩ := hn
  have had := comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have HC := (M n).bare_source_clock_bounds hcl hAz T (hb n) (hh n)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
  have hCf := bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have hterminal : ((M n).hf 1:ℝ)+((M n).bf 1:ℝ) ≤ B := by
    change ((M n).hf 1:ℝ)+((M n).bf 1:ℝ) ≤ 2*bareSourceClockConstant cl Az D+T
    have HH := HC.2.2.2
    have HB := HC.2.1
    have HX := mul_le_mul_of_nonneg_left ((hxs n).trans hnW1) hCf
    nlinarith only [HH,HB,HX]
  have Hlower := eventually_retainedStarMixedClock_lower n (M n).bf (M n).hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus (w n).star hstar
    (c:=3*T*c/8) (by positivity) hW hK
  have Hcoeff := eventually_native_star_recursion_coefficient_bound n (M n).bf (M n).hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus (w n).star hstar
    (c:=3*T*c/8) (by positivity) hW hK hterminal
  have Hcomp := eventually_retainedStarMixedClock_cubic_error n (M n).bf (M n).hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus (w n).star hstar
    hW zero_lt_one hcomp
  filter_upwards [Hlower,Hcoeff,Hcomp] with k hklo hkcoeff hkcomp
  have he : (3*T*c/8)/2=3*T*c/16 := by ring
  refine ⟨?_,hkcomp,?_⟩
  · simpa only [he] using hklo
  · simpa only [he] using hkcoeff

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
