module

public import ComparisonNativeActualHistoryOriginalScalarGapIntegralAlong
public import ComparisonNativeActualHistoryOriginalScalarGapPointwiseAlong
public import ComparisonSignedCavityActualPullbackFourProducers
public import ComparisonNativeActualComparableBandStarBond

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedVariables false

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N : ℕ→ℕ}

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_total_clock_and_root_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T) :
    ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T) ∧ (M n).h 0=0 := by
  exact G.total_root

theorem actual_selected_bad_history_continuum_scalar_limits_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T) :
    ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T,
      (M n).h 0=0 ∧
      ∀(us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass),u∈us →
      Tendsto (fun k=>nativeOriginalScalarPairMean (finiteCutMasses us k)
        (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
        (𝓝 (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val))) ∧
      Tendsto (fun k=>
        finitePhysicalMean (dim n+1) (finiteCutMasses us k)
          (retainedStarMatrix (M n).bf (finiteCutMasses us k))
          (retainedStarField (M n).hf (finiteCutMasses us k))
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
        nativeOriginalScalarPairMean (finiteCutMasses us k)
          (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us k))
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
        (𝓝 (orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
          scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val))) := by
  have hT : 0 < T := G.hT
  filter_upwards [actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M
    G] with n hn
  refine ⟨hn.1,hn.2,?_⟩
  intro us hus u hu
  exact ⟨(M n).inherited_continuum_retained_scalar_pair_tendsto hT hn.1 hn.2 us hus u hu,
    (M n).inherited_continuum_retained_scalar_mean_gap_tendsto hT hn.1 hn.2 us hus u hu⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000

namespace NativeOverlapMinimum

end NativeOverlapMinimum

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 16000000

theorem eventually_actual_selected_bad_history_original_continuum_scalar_remainder_comparable_context
    (Bclock Temp A c0 : ℝ) (hT : 0 ≤ Temp) (hA : 0 ≤ A) (hc0 : 0 < c0)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃R : ℝ,0 < R ∧ ∀ᶠn : ℕ in atTop,
      ∀(before after : List PositiveMass) (a : PositiveMass),
        MassOrdered 0 (before++a::after) →
      ∀j V : ℕ,j < before.length+1 → before.length+1 ≤ V →
        V ≤ (before++a::after).length →
        a.val < partitionPoint 0 (before++a::after) V →
        partitionPoint 0 (before++a::after) V ≤ A*(W n) →
      ∀(tree : ClockTree (Spin (dim n)×Bool) (before++a::after))
        (start : ℝ) (_hoa : MassOrdered start (before++a::after)) (s : tree.Slot),
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (before++a::after)
      let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree (before.length+1) K (p.embed s) p.mark)).sum
      |nativeOriginalScalarPairMean (before++a::after) K j-chi^2*K j| ≤
        nativeScalarLowRemainderConstant A R R*(W n)^3 := by
  exact eventually_actual_cavity_context_original_continuum_scalar_remainder A hA
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M
    G.toNativeActualCavityClockContext W hxs hWlim

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum

theorem exists_actual_selected_bad_history_sharp_window_sequence_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ctest c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n) := by
  exact exists_actual_comparable_context_sharp_window_sequence
    hm hdelta hroom hcl hcu hAz hC0 hCt hCtest hL dim hdim M G
    W hcanonical hWlim hcompare

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer NativeOverlapMinimum

theorem exists_actual_selected_bad_history_sharp_native_star_all_orders_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving := actualSlowWindowExponent m delta/64
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      ∀p : ℕ,∃Craw : ℝ,0 < Craw ∧ ActualNativeStarOrderSavingAlong p Craw saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨Cs,hCs,w,hw⟩ := exists_actual_selected_bad_history_sharp_window_sequence_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hL hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G
    W hcanonical hWlim hcompare
  have hc := actualSlowWindowExponent_pos hm hdelta hroom
  have hw0 : ∀ᶠn in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n) :=
    hw.mono fun _ h=>h.1
  refine ⟨by positivity,Cs,hCs,w,hw,?_⟩
  intro p
  exact eventually_actual_inherited_native_star_order_at_slow_window_along p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hCcal dim hdim M W hcanonical hWlim hcompare Cs hCs w hw0

theorem exists_actual_selected_bad_history_sharp_native_star_on_every_final_net_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving := actualSlowWindowExponent m delta/128
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      ∀A : ℕ,0 < A → ActualNativeStarFiniteDegreeOnEveryFinalNetAlong A saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,Cs,hCs,w,hw,H⟩ := exists_actual_selected_bad_history_sharp_native_star_all_orders_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim hcompare
  have hW n : 0 < W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_pos
  have Hfinal (p : ℕ) : ActualNativeStarMomentOnEveryFinalNetAlong p
      (actualSlowWindowExponent m delta/128) M W w := by
    obtain ⟨Craw,_,Horder⟩ := H p
    have HG := actual_native_star_order_saving_on_every_final_net_along p hs dim hdim M W hW w Horder
    simpa only [show (actualSlowWindowExponent m delta/64)/2=
      actualSlowWindowExponent m delta/128 by ring] using HG
  refine ⟨by linarith,Cs,hCs,w,hw,Hfinal,?_⟩
  intro A hA
  exact actual_native_star_final_net_to_finite_degrees_along A hA M W (fun n=>(hW n).le) w (Hfinal (A-1))

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 10000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_small_source_clocks_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T) :
    ∃Cf : ℝ,0 ≤ Cf ∧ ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf := by
  exact ⟨G.Cf,G.hCf,G.source⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum
set_option maxHeartbeats 14000000

theorem exists_actual_selected_bad_history_sharp_star_all_mixed_projection_powers_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
        (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong p
          (actualSlowWindowExponent m delta/128) M W w) ∧
        (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p saving M W w) ∧
        ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  obtain ⟨hs,Cs,hCs,w,hw,HnativeAlong,_⟩:=
    exists_actual_selected_bad_history_sharp_native_star_on_every_final_net_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
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

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem exists_actual_selected_bad_history_square_resource_pair_budgets_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
        (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
        ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
          (actualMassSavingExponent m delta/32) M W w ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
          ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong
            degree A saving Cmass M W w) ∧
        ∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hnative,_,_,Hmixed⟩:=
    exists_actual_selected_bad_history_sharp_star_all_mixed_projection_powers_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
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

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 18000000

theorem exists_actual_selected_bad_history_sharp_fresh_pair_feedback_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0 < saving ∧ 0 < sharpSaving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
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
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,Hpair,Hconstant⟩:=
    exists_actual_selected_bad_history_square_resource_pair_budgets_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
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

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 24000000

theorem exists_actual_selected_bad_history_four_numeric_inputs_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0 < saving ∧ 0 < sharpSaving ∧ ∃cK : ℝ,0 < cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
        (∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
        (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
        ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong sharpSaving M W w ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
          ∃A : ℝ,1 ≤ A ∧
            ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w ∧
            ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong
              degree A saving sharpSaving Cmass M W w ∧
            ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong
              degree A saving sharpSaving Cmass M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀depth : ℕ,
          ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀k0 depth r : ℕ,
          ActualOriginalFourInitialPairForestSavingAlong k0 depth r saving sharpSaving Cmass M W w) ∧
        (∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w ∧
          ActualOriginalConstantFreshPairSavingOnEveryFinalNetAlong degree saving sharpSaving M W w ∧
          ActualOriginalConstantFourPairContrastSavingOnEveryFinalNetAlong degree saving sharpSaving M W w) ∧
        (∀k0 depth r : ℕ,0 < k0+depth →
          ActualOriginalConstantFourPairForestSavingAlong k0 depth r saving sharpSaving M W w) ∧
        (∀k0 depth r : ℕ,ActualOriginalFourConstantFrozenChildLevelSavingAlong
          k0 depth r saving M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass →∃threshold : ℕ,0 < threshold ∧∃terminalSaving : ℝ,
          0 < terminalSaving ∧∀depth : ℕ,threshold ≤ depth→
            ActualOriginalContinuumNaturalCenteredFourGTerminalSavingAlong depth terminalSaving Cmass M W w) ∧
        (∀r : ℕ,∃threshold : ℕ,0 < threshold ∧∃terminalSaving : ℝ,
          0 < terminalSaving ∧∀depth : ℕ,threshold ≤ depth→
            ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong r depth terminalSaving M W w) ∧
        ∃Cb : ℝ,0 < Cb ∧∀ᶠn in atTop,∀(as : List PositiveMass)
          (_ho : MassOrdered 0 as),(w n).star∈as→
          ∀U : ℕ,retainedMassPrefixIndex (w n).star.val as < U→U ≤ as.length→
            let star:=retainedMassPrefixIndex (w n).star.val as
            let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
            let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
            |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤
              |T*chi^2-1|+Cb*(W n)^2 := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,hsharp,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,Hpair,Hconstant⟩:=
    exists_actual_selected_bad_history_sharp_fresh_pair_feedback_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  let cK:=3*T*(starMassBandConstant cu Az/cu)/8
  have hcK : 0 < cK := by
    dsimp only [cK]
    exact div_pos (mul_pos (mul_pos (by norm_num) hTemp)
      (div_pos (star_mass_band_constant_pos hcu hAz) hcu)) (by norm_num)
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M
    G
  have HK : ∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    filter_upwards [hw] with n hn
    obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,Hclock,_⟩:=hn.1
    exact Hclock
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,Cs,hCs,w,hw,HK,
    Hsquare,Hmixed,Hsharp,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro Cmass hCm degree hd
    obtain ⟨A,hA,HP,HF⟩:=Hpair Cmass hCm degree hd
    exact ⟨A,hA,HP,HF,actual_original_four_pair_contrast_saving_of_fresh_feedback_along degree A M W w HF⟩
  · intro Cmass hCm depth
    obtain ⟨A,hA,HP,_⟩:=Hpair Cmass hCm (depth+2) (by omega)
    exact actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
      hm hC0 (by linarith) hs hcK depth hA Cmass dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK HP
  · intro Cmass hCm k0 depth r
    obtain ⟨A,hA,_,HF⟩:=Hpair Cmass hCm (1+k0+depth) (by omega)
    exact actual_inherited_four_initial_pair_forest_saving_along (by linarith) hsharp hcK
      k0 depth r hA Cmass dim hdim M W hxs (Htotal.mono (fun _ hn=>hn.1)) w HK
      (actual_original_four_pair_contrast_saving_of_fresh_feedback_along (1+k0+depth) A M W w HF)
  · intro degree hd
    obtain ⟨HP,HF⟩:=Hconstant degree hd
    exact ⟨HP,HF,actual_original_constant_four_pair_contrast_saving_of_fresh_feedback_along degree M W w HF⟩
  · intro k0 depth r hd
    exact actual_inherited_constant_four_pair_forest_saving_along (by linarith) hsharp hcK
      k0 depth r dim hdim M W hxs (Htotal.mono (fun _ hn=>hn.1)) w HK
      (actual_original_constant_four_pair_contrast_saving_of_fresh_feedback_along (k0+depth) M W w
        (Hconstant (k0+depth) hd).2)

  · intro k0 depth r
    exact actual_inherited_four_constant_frozen_child_level_saving_of_pair_budget_along
      hm hC0 (by linarith) hcK k0 depth r (by norm_num) dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK
      (Hconstant (k0+depth+1) (by omega)).1
  · intro Cmass hCm
    exact exists_actual_sharp_same_star_natural_centered_four_G_terminal_along
      hm hcu hAz hC0 (by linarith) hTemp hs Cmass dim hdim M W hxs hWlim
      (Htotal.mono (fun _ hn=>hn.1)) w hw (fun degree hd=>by
        obtain ⟨A,hA,HP,_⟩:=Hpair Cmass hCm degree hd
        exact ⟨A,hA,HP⟩)
  · intro r
    exact exists_actual_sharp_same_star_generated_constant_four_G_terminal_along
      hm hcu hAz hC0 (by linarith) hTemp hs r dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) w hw (fun degree hd=>(Hconstant degree hd).1)
  · exact actual_selected_bad_history_susceptibility_coefficient_along_comparable_context (c0:=c0)
      hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim w hw

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem exists_actual_selected_bad_history_constant_source_four_inputs_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0<saving ∧ 0<sharpSaving ∧∃cK : ℝ,0<cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0≤Cf ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0<Cs ∧∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0<degree→
        ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenPairLevelSavingAlong depth saving sharpSaving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong depth saving M W w) ∧
      ActualOriginalConstantSourceChildrenFrozenSavingAlong saving M W w ∧
      ∃threshold : ℕ,0<threshold ∧∃terminalSaving : ℝ,0<terminalSaving ∧
        ∀depth : ℕ,threshold≤depth→
          ActualOriginalConstantSourceChildrenFourTerminalSavingAlong depth terminalSaving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,Cs,hCs,w,hw,HK,Hsquare,Hmixed,
    _Hsharp,_Hinitial,_HinitialFrozen,_HinitialPair,Hconstant,HconstantPair,HconstantFrozen,
    _HinitialTerminal,HconstantTerminal,_Hbond⟩:=
    exists_actual_selected_bad_history_four_numeric_inputs_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Htotal' := Htotal.mono (fun _ hn=>hn.1)
  have Hroot := Htotal.mono (fun _ hn=>hn.2)
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,Cs,hCs,w,hw,HK,Hsquare,Hmixed,
    fun degree hd=>(Hconstant degree hd).1,?_,?_,?_,?_⟩
  · intro depth
    exact (HconstantPair 1 depth 3 (by omega)).source_children hxs Htotal'
  · intro depth
    exact (HconstantFrozen 1 depth 3).source_children Htotal'
  · exact actual_inherited_constant_source_children_frozen_saving_of_pair_budget_along
      hm hC0 (by linarith) (by norm_num : (1:ℝ)≤1) dim hdim M W hxs Htotal' Hroot w
      (Hconstant 1 (by norm_num)).1
  · obtain ⟨threshold,hthreshold,saving,hsaving,Hterm⟩:=HconstantTerminal 3
    exact ⟨threshold,hthreshold,saving,hsaving,fun depth hd=>(Hterm depth hd).source_children Htotal'⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_all_mixed_projection_powers_at_sharp_window_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (_hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (_hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
        (∀p : ℕ,ActualNativeStarMomentOnEveryFinalNetAlong p
          (actualSlowWindowExponent m delta/128) M W w) ∧
        (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNetAlong p saving M W w) ∧
        ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
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

theorem actual_selected_bad_history_square_resource_pair_budgets_at_sharp_window_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
        (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
        ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
          (actualMassSavingExponent m delta/32) M W w ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
          ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong
            degree A saving Cmass M W w) ∧
        ∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,Cf,hCf,Hsource,hw,Hnative,_,_,Hmixed⟩:=
    actual_selected_bad_history_all_mixed_projection_powers_at_sharp_window_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare Cs hCs w hw
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

theorem actual_selected_bad_history_sharp_fresh_pair_feedback_at_sharp_window_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0 < saving ∧ 0 < sharpSaving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
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
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,Cf,hCf,Hsource,hw,Hsquare,Hmixed,Hsharp,Hpair,Hconstant⟩:=
    actual_selected_bad_history_square_resource_pair_budgets_at_sharp_window_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare Cs hCs w hw
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

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_four_numeric_inputs_at_sharp_window_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0 < saving ∧ 0 < sharpSaving ∧ ∃cK : ℝ,0 < cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
        (∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
        (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
        ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong sharpSaving M W w ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
          ∃A : ℝ,1 ≤ A ∧
            ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w ∧
            ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong
              degree A saving sharpSaving Cmass M W w ∧
            ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong
              degree A saving sharpSaving Cmass M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀depth : ℕ,
          ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀k0 depth r : ℕ,
          ActualOriginalFourInitialPairForestSavingAlong k0 depth r saving sharpSaving Cmass M W w) ∧
        (∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w ∧
          ActualOriginalConstantFreshPairSavingOnEveryFinalNetAlong degree saving sharpSaving M W w ∧
          ActualOriginalConstantFourPairContrastSavingOnEveryFinalNetAlong degree saving sharpSaving M W w) ∧
        (∀k0 depth r : ℕ,0 < k0+depth →
          ActualOriginalConstantFourPairForestSavingAlong k0 depth r saving sharpSaving M W w) ∧
        (∀k0 depth r : ℕ,ActualOriginalFourConstantFrozenChildLevelSavingAlong
          k0 depth r saving M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass →∃threshold : ℕ,0 < threshold ∧∃terminalSaving : ℝ,
          0 < terminalSaving ∧∀depth : ℕ,threshold ≤ depth→
            ActualOriginalContinuumNaturalCenteredFourGTerminalSavingAlong depth terminalSaving Cmass M W w) ∧
        (∀r : ℕ,∃threshold : ℕ,0 < threshold ∧∃terminalSaving : ℝ,
          0 < terminalSaving ∧∀depth : ℕ,threshold ≤ depth→
            ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong r depth terminalSaving M W w) ∧
        ∃Cb : ℝ,0 < Cb ∧∀ᶠn in atTop,∀(as : List PositiveMass)
          (_ho : MassOrdered 0 as),(w n).star∈as→
          ∀U : ℕ,retainedMassPrefixIndex (w n).star.val as < U→U ≤ as.length→
            let star:=retainedMassPrefixIndex (w n).star.val as
            let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
            let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
            |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤
              |T*chi^2-1|+Cb*(W n)^2 := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,hsharp,Cf,hCf,Hsource,hw,Hsquare,Hmixed,Hsharp,Hpair,Hconstant⟩:=
    actual_selected_bad_history_sharp_fresh_pair_feedback_at_sharp_window_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare Cs hCs w hw
  let cK:=3*T*(starMassBandConstant cu Az/cu)/8
  have hcK : 0 < cK := by
    dsimp only [cK]
    exact div_pos (mul_pos (mul_pos (by norm_num) hTemp)
      (div_pos (star_mass_band_constant_pos hcu hAz) hcu)) (by norm_num)
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M
    G
  have HK : ∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    filter_upwards [hw] with n hn
    obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,Hclock,_⟩:=hn.1
    exact Hclock
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,hw,HK,
    Hsquare,Hmixed,Hsharp,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro Cmass hCm degree hd
    obtain ⟨A,hA,HP,HF⟩:=Hpair Cmass hCm degree hd
    exact ⟨A,hA,HP,HF,actual_original_four_pair_contrast_saving_of_fresh_feedback_along degree A M W w HF⟩
  · intro Cmass hCm depth
    obtain ⟨A,hA,HP,_⟩:=Hpair Cmass hCm (depth+2) (by omega)
    exact actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
      hm hC0 (by linarith) hs hcK depth hA Cmass dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK HP
  · intro Cmass hCm k0 depth r
    obtain ⟨A,hA,_,HF⟩:=Hpair Cmass hCm (1+k0+depth) (by omega)
    exact actual_inherited_four_initial_pair_forest_saving_along (by linarith) hsharp hcK
      k0 depth r hA Cmass dim hdim M W hxs (Htotal.mono (fun _ hn=>hn.1)) w HK
      (actual_original_four_pair_contrast_saving_of_fresh_feedback_along (1+k0+depth) A M W w HF)
  · intro degree hd
    obtain ⟨HP,HF⟩:=Hconstant degree hd
    exact ⟨HP,HF,actual_original_constant_four_pair_contrast_saving_of_fresh_feedback_along degree M W w HF⟩
  · intro k0 depth r hd
    exact actual_inherited_constant_four_pair_forest_saving_along (by linarith) hsharp hcK
      k0 depth r dim hdim M W hxs (Htotal.mono (fun _ hn=>hn.1)) w HK
      (actual_original_constant_four_pair_contrast_saving_of_fresh_feedback_along (k0+depth) M W w
        (Hconstant (k0+depth) hd).2)

  · intro k0 depth r
    exact actual_inherited_four_constant_frozen_child_level_saving_of_pair_budget_along
      hm hC0 (by linarith) hcK k0 depth r (by norm_num) dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK
      (Hconstant (k0+depth+1) (by omega)).1
  · intro Cmass hCm
    exact exists_actual_sharp_same_star_natural_centered_four_G_terminal_along
      hm hcu hAz hC0 (by linarith) hTemp hs Cmass dim hdim M W hxs hWlim
      (Htotal.mono (fun _ hn=>hn.1)) w hw (fun degree hd=>by
        obtain ⟨A,hA,HP,_⟩:=Hpair Cmass hCm degree hd
        exact ⟨A,hA,HP⟩)
  · intro r
    exact exists_actual_sharp_same_star_generated_constant_four_G_terminal_along
      hm hcu hAz hC0 (by linarith) hTemp hs r dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) w hw (fun degree hd=>(Hconstant degree hd).1)
  · exact actual_selected_bad_history_susceptibility_coefficient_along_comparable_context (c0:=c0)
      hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim w hw

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_constant_source_four_inputs_at_sharp_window_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0<saving ∧ 0<sharpSaving ∧∃cK : ℝ,0<cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0≤Cf ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0<degree→
        ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenPairLevelSavingAlong depth saving sharpSaving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong depth saving M W w) ∧
      ActualOriginalConstantSourceChildrenFrozenSavingAlong saving M W w ∧
      ∃threshold : ℕ,0<threshold ∧∃terminalSaving : ℝ,0<terminalSaving ∧
        ∀depth : ℕ,threshold≤depth→
          ActualOriginalConstantSourceChildrenFourTerminalSavingAlong depth terminalSaving M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,hw,HK,Hsquare,Hmixed,
    _Hsharp,_Hinitial,_HinitialFrozen,_HinitialPair,Hconstant,HconstantPair,HconstantFrozen,
    _HinitialTerminal,HconstantTerminal,_Hbond⟩:=
    actual_selected_bad_history_four_numeric_inputs_at_sharp_window_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare Cs hCs w hw
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Htotal' := Htotal.mono (fun _ hn=>hn.1)
  have Hroot := Htotal.mono (fun _ hn=>hn.2)
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,hw,HK,Hsquare,Hmixed,
    fun degree hd=>(Hconstant degree hd).1,?_,?_,?_,?_⟩
  · intro depth
    exact (HconstantPair 1 depth 3 (by omega)).source_children hxs Htotal'
  · intro depth
    exact (HconstantFrozen 1 depth 3).source_children Htotal'
  · exact actual_inherited_constant_source_children_frozen_saving_of_pair_budget_along
      hm hC0 (by linarith) (by norm_num : (1:ℝ)≤1) dim hdim M W hxs Htotal' Hroot w
      (Hconstant 1 (by norm_num)).1
  · obtain ⟨threshold,hthreshold,saving,hsaving,Hterm⟩:=HconstantTerminal 3
    exact ⟨threshold,hthreshold,saving,hsaving,fun depth hd=>(Hterm depth hd).source_children Htotal'⟩

theorem actual_selected_bad_history_constant_source_known_envelope_at_sharp_window_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0<saving ∧ 0<sharpSaving ∧∃cK : ℝ,0<cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0≤Cf ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0<degree→
        ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenPairLevelSavingAlong depth saving sharpSaving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong depth saving M W w) ∧
      ActualOriginalConstantSourceChildrenFrozenSavingAlong saving M W w ∧
      ∃threshold : ℕ,0<threshold ∧∃terminalSaving : ℝ,0<terminalSaving ∧
        ∀depth : ℕ,threshold≤depth→
          ActualOriginalConstantSourceChildrenFourTerminalSavingAlong depth terminalSaving M W w ∧
          ActualConstantSourceKnownEnvelopeAlong T cK saving sharpSaving terminalSaving depth M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,hw,HK,Hsquare,Hmixed,Hconstant,
    Hpair,Hfrozen,Hinitial,threshold,hthreshold,tau,htau,Hterm⟩:=
    actual_selected_bad_history_constant_source_four_inputs_at_sharp_window_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare Cs hCs w hw
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,hw,HK,Hsquare,Hmixed,Hconstant,
    Hpair,Hfrozen,Hinitial,threshold,hthreshold,tau,htau,?_⟩
  intro depth hd
  refine ⟨Hterm depth hd,?_⟩
  exact actual_constant_source_known_envelope_along hcK depth M W hxs
    (Htotal.mono (fun _ hn=>hn.1)) w HK
    (fun j _=>Hpair j) (fun j _=>Hfrozen j) Hinitial (Hterm depth hd)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
set_option maxHeartbeats 14000000

theorem actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(M n).actualOriginalLowErrorDensitySaving C) atTop (𝓝 0) := by
  have Hps := G.pullback
  have Hclock := G.pullback
  exact actualOriginalLowErrorDensitySaving_regular_tendsto_zero_along hm hdelta hroom hcl hcu hAz
    hC0 hCt hCompare dim hdim M hsmall hWlim Hclock C hC

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 14000000

theorem actual_second_low_inherited_constant_B0_amplitude_tendsto_zero_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Couter C Ccompare c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare) (hCouter : 0 ≤ Couter)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    Tendsto (fun n=>actualSecondLowOriginalConstantB0Amplitude (M n) Temp Cf Couter C)
      atTop (𝓝 0) := by
  have HS:=actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M G
    hsmall hWlim (Couter+1) (by linarith)
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along hm hC0 dim hdim M
  have heta : 0 < actualMassSavingExponent m delta/32 :=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have HP:=(tendsto_rpow_neg_atTop heta).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have H:=HP.const_mul 16 |>.add
    ((HS.add HI).const_mul (C*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp))
  simpa only [actualSecondLowOriginalConstantB0Amplitude,Function.comp_def,add_zero,mul_zero] using H

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 50000000

theorem actual_history_second_low_fresh_replacement_amplitude_tendsto_zero_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Couter Cstar Csaved Cmoving Ccompare c0 : ℝ}
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCompare : 0≤Ccompare) (hCouter : 0≤Couter)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    Tendsto (fun n=>actualHistorySecondLowFreshReplacementAmplitude (M n)
      eta Temp Cf Couter Cstar Csaved Cmoving) atTop (𝓝 0) := by
  have HD:=actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M G
    hsmall hWlim (Couter+1) (by linarith)
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero_along hm hC0 dim hdim M
  have Hstar:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
    (by norm_num : (0:ℝ)<32))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hsaved:=(tendsto_rpow_neg_atTop heta).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have H:=((Hstar.const_mul Cstar).add (Hsaved.const_mul Csaved)).add
    ((HD.add HI).const_mul (Cmoving*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp))
  simpa only [actualHistorySecondLowFreshReplacementAmplitude,Function.comp_def,mul_zero,add_zero] using H

theorem actual_second_low_actual_history_fresh_B0_modulo_replacement_modulus_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal : ℝ)
    (hTemp : 0≤Temp) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter) (hCcal : 1≤Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta<6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0≤Cf ∧ 0<Ci ∧ ∃eps : ℕ→ℝ,(∀n,0≤eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFreshReplacementModulusOnEveryFinalNetAlong degree rBound Cmass Ccut Couter
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w := by
  obtain ⟨Cf,hCf,HS⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0) hm hdelta hcl hAz hC0 hc0
    hmargin hcapmargin dim hdim M G
  obtain ⟨Ci,Cm,Csaved,Cstar,hCi,hCmRate,hCsaved,hCstar,H⟩:=
    actual_second_low_fresh_B0_modulo_c_replacement_budget_along degree rBound Cmass Ccut Couter Ccal
      hTemp hCf hCm hCcut hCouter hCcal heta.le hm hdelta hroom hgap hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim w HS Hcompare hw
  let eps:=fun n=>actualHistorySecondLowFreshReplacementAmplitude (M n) eta Temp Cf Couter Cstar Csaved Cm
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE]
    exact hWlim
  refine ⟨Cf,Ci,hCf,hCi,eps,?_,actual_history_second_low_fresh_replacement_amplitude_tendsto_zero_along_comparable_context (c0:=c0)
    heta hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hCouter dim hdim M
    G Hcompare HL,?_⟩
  · intro n
    have HD:0 < (M n).actualOriginalLowErrorDensitySaving (Couter+1):=
      (M n).actualOriginalLowErrorDensitySaving_pos (by linarith)
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    dsimp [eps,actualHistorySecondLowFreshReplacementAmplitude]
    positivity
  · filter_upwards [H] with n hn
    intro L us hus hstar hret hmesh
    filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
    dsimp only at hgrid ⊢
    intro i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
      G forms initial x hxsx hxW hmass s
    have HB:=hgrid i V U T hU hV hiV hVstar hstarU hpersistent hcut hT houter hWU hRstar hz
      G forms initial x hxsx hxW hmass s
    let as:=finiteCutMasses us jGrid
    let p0:=sourceMonomialScale x (W n) initial
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hx:0 < (M n).xs:=(M n).hxs
    have hW:0 < W n:=hx.trans_le (hxsx.trans hxW)
    have hp0:0≤p0:=by
      dsimp [p0]
      rw [←source_factor_scale_product]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (hx.trans_le hxsx) hW initial e).le
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    have Hrho:(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
        partitionPoint 0 as U/(dim n+1:ℕ)≤
        ((M n).actualOriginalLowErrorDensitySaving (Couter+1)+(1/(dim n+1:ℕ):ℝ)/(M n).xs^2)*(M n).xs^2:=by
      rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (partitionPoint_mem as ho U).2 (by positivity))
    have Hr:=mul_le_mul_of_nonneg_left Hrho
      (mul_nonneg (mul_nonneg (mul_nonneg hCmRate.le hW.le) HCerr) hp0)
    apply HB.trans
    dsimp [eps,actualHistorySecondLowFreshReplacementAmplitude]
    convert add_le_add_left Hr
      (Ci*partitionPoint 0 as U*(M n).xs*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))*p0+
        Cstar*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2*p0+
        Csaved*((dim n+1:ℕ):ℝ)^(-eta)*W n*(M n).xs^2*p0) using 1 <;> ring

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum

theorem actual_second_low_full_centered_B0_amplitude_tendsto_zero_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Couter Cstar Csaved Cmoving Crep Ccompare c0 : ℝ}
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCompare : 0≤Ccompare) (hCouter : 0≤Couter)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    Tendsto (fun n=>actualSecondLowFullCenteredB0Amplitude (M n)
      eta Temp Cf Couter Cstar Csaved Cmoving Crep) atTop (𝓝 0) := by
  have HA:=actual_history_second_low_fresh_replacement_amplitude_tendsto_zero_along_comparable_context (c0:=c0)
    heta hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hCouter dim hdim M
    G hsmall hWlim
    (Temp:=Temp) (Cf:=Cf) (Cstar:=Cstar) (Csaved:=Csaved) (Cmoving:=Cmoving)
  have HR:=classified_dyadic_fold_saving_amplitude_tendsto_zero_along Crep eta heta dim hdim
  simpa only [actualSecondLowFullCenteredB0Amplitude,add_zero] using HA.add HR

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem actual_second_low_actual_history_full_resource_B0_modulus_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter) (hCcal : 1 ≤ Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0 ≤ Cf ∧ 0 < Ci ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∃eps : ℕ→ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFullResourceB0ModulusOnEveryFinalNetAlong degree rBound Cmass Ccut Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w := by
  classical
  obtain ⟨Cf,hCf,HS⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0) hm hdelta hcl hAz hC0 hc0
    hmargin hcapmargin dim hdim M G
  have HP (a : Fin (degree+1)):=actual_second_low_full_centered_B0_modulus_along a.val rBound
    Cmass Ccut Couter Ccal Rmacro F Cx hCx heta hTemp hCf hCm hCcut hCouter hCcal hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim M W hcanonical hWlim w HS Hcompare hw
  choose Ci Cm Csaved Cstar Crep hCi hCmRate hCsaved hCstar hCrep HC using HP
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget (D:=D)
    (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  let CI:=1+∑a,Ci a
  have hCI : 0 < CI:=by
    have HH : 0 ≤ ∑a : Fin (degree+1),Ci a:=Finset.sum_nonneg (fun a _=>(hCi a).le)
    dsimp only [CI];linarith
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  let amp:=fun a n=>actualSecondLowFullCenteredB0Amplitude (M n) eta Temp Cf Couter (Cstar a) (Csaved a) (Cm a) (Crep a)
  have hamp a n : 0 ≤ amp a n:=actual_second_low_full_centered_B0_amplitude_nonneg (M n) eta Temp Cf Couter _ _ _ _
    hTemp hCouter (hCstar a).le (hCsaved a).le (hCmRate a).le (hCrep a).le
  let eps:=fun n=>A^degree*∑a,amp a n
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE];exact hWlim
  have Hamp a : Tendsto (amp a) atTop (𝓝 0):=actual_second_low_full_centered_B0_amplitude_tendsto_zero_along_comparable_context (c0:=c0) heta hm hdelta hroom
    hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hCouter dim hdim M G Hcompare HL
  have Heps : Tendsto eps atTop (𝓝 0):=by
    have HH:=(tendsto_finsetSum Finset.univ (fun a _=>Hamp a)).const_mul (A^degree)
    simpa only [Finset.sum_const_zero,mul_zero] using HH
  refine ⟨Cf,A^degree*CI,hCf,by positivity,HS,eps,?_,Heps,?_⟩
  · intro n
    exact mul_nonneg (pow_nonneg hA0.le _) (Finset.sum_nonneg (fun a _=>hamp a n))
  · have HX : ∀ᶠn in atTop,(M n).xs ≤ 1:=by
      filter_upwards [hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with n hn
      rw [hcanonical n] at hn
      exact (M n).canonical_direct_test_band_ge_scale.trans hn
    filter_upwards [Filter.eventually_all.mpr HC,hdim.eventually HA,HS,HX] with n hnC hnA hnS hnX
    intro L us hus hstar hret hmesh
    filter_upwards [Filter.eventually_all.mpr (fun a : Fin (degree+1)=>hnC a L us hus hstar hret hmesh),
      hnA (M n) hnS hnX L us hus hret hmesh] with jGrid hgC hgA
    dsimp only at hgC hgA ⊢
    intro pre mid tail hparts hindex V U k T hU seed P hP hdegree hmid hV hiV hVstar hs hT hcut houter
      x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
    have Hdyadic:=native_second_low_coarse_readout_from_retained_nodes sourceMass hsourceMass us hus Hnodes
      jGrid U (by simpa only [hparts] using hU) HsourceMass
    rw [hparts] at hgC hgA hindex hcut houter hmi hms Hhigh Hz Hri Hrs Hdyadic ⊢
    let as:=pre++(mid++tail)
    have hi : pre.length ≤ pre.length+mid.length:=by omega
    have hstar : pre.length+mid.length < as.length:=hs.trans_le hU
    have hdepth : seed.length+k ≤ degree:=by rw [←hP.total_factor_depth];exact hdegree
    have hLive : P.live.factors.length ≤ degree:=by
      have HH : P.live.tags.length ≤ P.resources.length:=by simp only [NativeResourceTerm.resources,List.length_append];omega
      simp only [NativeResourceMonomial.tags,List.length_map] at HH
      exact HH.trans hdegree
    let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
    let G:=nativeActualResourceCanonicalShape P.live hi hstar
    let initial:=nativeActualResourceInitialFactors P.live
    let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
    let AI:=partitionPoint 0 as U*(M n).xs*Cerr*
      (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))
    let AX:=W n*(M n).xs^2
    let price:=Ci a*AI+amp a n*AX
    have ho:MassOrdered 0 as:=by
      dsimp only [as]
      rw [←hparts]
      exact finiteCutMasses_ordered us hus jGrid
    have hxs0 : 0 < (M n).xs:=(M n).hxs
    have hx0 : 0 < x:=hxs0.trans_le hx
    have hW : 0 < W n:=hx0.trans_le hxW
    have hmassU : 0 ≤ partitionPoint 0 as U:=(partitionPoint_mem as ho U).1
    have hCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
    have hdi : 0 ≤ nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length:=Real.sqrt_nonneg _
    have hAI : 0 ≤ AI:=by dsimp only [AI];positivity
    have hAX : 0 ≤ AX:=by dsimp only [AX];positivity
    have hprice : 0 ≤ price:=add_nonneg (mul_nonneg (hCi a).le hAI) (mul_nonneg (hamp a n) hAX)
    have Hbare:=hgC a pre mid tail rfl T G (fun _=>NativeSourceFactorForm.centered) initial P.live.test.target U hU V
      x sourceMass hsourceMass hindex hmid hV hiV hVstar hs (hP.persistentLowForks hi) hT hcut houter hx hxW
      (native_actual_resource_canonical_factors_LOW P.live hi hs hU)
      (native_actual_resource_canonical_source_mass P.live hi hstar Cmass x (W n) hmi hms)
      (hmi.trans (mul_le_mul_of_nonneg_left hxW hCm)) hms Hhigh Hz
      (native_actual_resource_canonical_source_radius_gate (M n) P.live hi hstar _ Hri Hrs) Hri Hrs HCx Hdyadic
    rw [native_actual_resource_live_scale_eq_annotations] at Hbare
    have Hpair:=hgA U pre.length (pre.length+mid.length) T P (hdegree.trans (by omega))
      (hi.trans hstar.le) hstar.le x (W n) hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
    have HB:=actual_resource_full_B0_normalized_profile_le (M n) hP hdepth ho hi hstar hA hx hxW hprice Hpair
      (by
        dsimp only
        rw [show nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as=
          (fun j=>(M n).hf (partitionPoint 0 as j)+(M n).bf (partitionPoint 0 as j)*
            orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)) by rfl]
        unfold nativeSecondLowFreshFullB0Source
        dsimp only
        convert Hbare using 1; dsimp only [AI,AX,price,amp,Cerr,as]; ring)
    have HCi : Ci a ≤ CI:=by
      have HH:=Finset.single_le_sum (fun a _=>(hCi a).le) (Finset.mem_univ a)
      dsimp only [CI];linarith
    have Hsum : amp a n ≤ ∑b,amp b n:=Finset.single_le_sum (fun b _=>hamp b n) (Finset.mem_univ a)
    have HD:=add_le_add (mul_le_mul_of_nonneg_right HCi hAI) (mul_le_mul_of_nonneg_right Hsum hAX)
    have hscale : 0 ≤ nativeResourceScale x (W n) 1 seed:=(actual_resource_raw_scale_pos seed hx0 hW).le
    apply HB.trans
    have HH:=mul_le_mul_of_nonneg_left HD
      (show 0 ≤ |P.coefficient| *A^degree*nativeResourceScale x (W n) 1 seed by positivity)
    convert HH using 1; dsimp only [AI,AX,price,eps,Cerr]; ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 40000000
set_option backward.isDefEq.respectTransparency false

theorem actual_second_low_actual_history_full_half_retarget_B0_modulus_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter Ccal Rmacro F Cx : ℝ)
    (hCx : 0 < Cx) (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter) (hCcal : 1 ≤ Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0 ≤ Cf ∧ 0 < Ci ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∃eps : ℕ→ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong degree rBound Cmass Ccut Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w := by
  obtain ⟨Cf,Ci,hCf,hCi,HS,eps,heps,HL,H⟩:=actual_second_low_actual_history_full_resource_B0_modulus_along_comparable_context (c0:=c0)
    degree (rBound+1) Cmass Ccut Couter Ccal Rmacro F Cx hCx hTemp hCm hCcut hCouter hCcal
    heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hc0 hmargin hcapmargin
    dim hdim M G W hcanonical hWlim w Hcompare hw
  refine ⟨Cf,(3/2:ℝ)*Ci,hCf,by positivity,HS,fun n=>(3/2:ℝ)*eps n,?_,?_,?_⟩
  · intro n;exact mul_nonneg (by norm_num) (heps n)
  · simpa only [mul_zero] using HL.const_mul (3/2:ℝ)
  · exact actual_second_low_full_half_retarget_from_actual_resource_rows_along degree rBound
      Cmass Ccut Couter Rmacro Cx (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w H

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 26000000
variable {dim : ℕ → ℕ}

theorem actual_selected_bad_history_constant_source_first_high_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceFirstHighOnGivenCutsAlong depth C M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_constant_source_first_high_rate_of_pullback_clocks
    (D:=D) depth Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu) cK
    hTemp hCf hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*W n ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,Hps,Htotal,Hcuts,hcompare,HW,HG]
    with n hn hs hp ht hcuts hcomp hw hg
  intro L us hus hret hmesh hstar hhigh houter
  have H:=hn (M n) Temp 
    hp hs ht.1 hcomp
    (by norm_num;simpa only [hcanonical n] using hw) (by norm_num;simpa only [hcanonical n,one_div] using hg)
    L us hus hret hmesh
  filter_upwards [H] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  have hW : 0 ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos.le
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW)
  have HH:=hj _ _ Hs (HUV.le.trans HV)
    (by simpa only [hcanonical n] using Hfirst)
    (by simpa only [hcanonical n] using Hmass') (by simpa only [hcanonical n] using HK)
  simpa only [hcanonical n] using HH

theorem actual_selected_bad_history_constant_source_rates_on_given_cuts_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (heta : 0 < eta) (hgap : 2*eta < 6*m)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ → ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃Cg Cf : ℝ,0 < Cg ∧ 0 < Cf ∧
      ActualConstantSourceGaCurrentOnGivenCutsAlong depth eta Cg M W w high outer ∧
      ActualConstantSourceFirstHighOnGivenCutsAlong depth Cf M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cfield,hCfield,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  obtain ⟨Cg,hCg,HG⟩:=eventually_inherited_same_star_constant_source_Ga_current_along hdim
    depth Cmass cK hCm hcK heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hTemp hCfield hCcal M W hcanonical hWlim hcompare Hsource
    (Htotal.mono (fun _ h=>h.1)) saving hsaving w Hmixed
  obtain ⟨Cf,hCf,HF⟩:=actual_selected_bad_history_constant_source_first_high_on_given_cuts_along_comparable_context (c0:=c0)
    depth Cmass (zero_le_one.trans hCm) hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCcal hc0 hmargin hcapmargin hdim M G
    W radius hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  exact ⟨Cg,Cf,hCg,hCf,HG.on_given_cuts
    (fun n=>(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm) hA Hcuts,HF⟩

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 26000000
variable {dim : ℕ → ℕ}

theorem actual_selected_bad_history_constant_source_restoration_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceGaRestorationOnGivenCutsAlong depth C M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_constant_child_G_restoration_forest_rate_along_of_pullback_clocks
    dim hdim depth Bclock Temp Cf Cmass Cmass cK hTemp hCf hCm hCm hcK
    (D:=D) (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,Hsource,Hps,Htotal,Hcuts,hcompare,HW] with n hn hs hp ht hcuts hcomp hw
  intro L us hus hret hmesh hstar hhigh houter
  have H:=hn (M n) Temp 
    hs hp ht.1 hcomp (by simpa only [hcanonical n] using hw) L us hus hret hmesh
  filter_upwards [H] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,Houter,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  have hW : 0 ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos.le
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW)
  have Hhigh':=(partitionPoint_mono _ (finiteCutMasses_ordered us hus j) HUV.le).trans
    (Houter.trans (mul_le_mul_of_nonneg_right hA hW))
  have HH:=hj _ _ Hs (HUV.le.trans HV)
    (by simpa only [hcanonical n] using Hfirst) (by simpa only [hcanonical n] using Hhigh')
    (by simpa only [hcanonical n] using Hmass') (by simpa only [hcanonical n] using HK)
  rw [show nativeActualMinimumFourCenteredForest (M n) Hs (HUV.le.trans HV) (W n) depth
    (nativeActualConstantSourceChildren (M n) (finiteCutMasses us j)
      (retainedMassPrefixIndex (w n).star.val (finiteCutMasses us j))
      (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) Hs (HUV.le.trans HV)) = _ from
      nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _]
  simpa only [hcanonical n,nativeActualMinimumFourCenteredForest] using HH

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_selected_bad_history_deleted_site_forest_rate_along_comparable_context
    (seedBound k₀ r₀ depth : ℕ) (Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(U i star : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin (dim n)×Bool) as i star),
          seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term → i ≤ star →
        ∀(hs : star < U) (hU : U ≤ as.length),
        ∀x : ℝ,(M n).xs ≤ x → x ≤ W n →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W n →
          cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
          |nativeActualFourOtherCategorySum (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]) .deletedSite| ≤
            C*|st.term.coefficient| *((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W n*(M n).xs^2)*
              nativeResourceScale x (W n) 1 seed := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_inherited_deleted_site_forest_rate
    (D:=D) seedBound k₀ r₀ depth Bclock Temp Cf Cmass cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,HW] with n hn hs hw
  have hxs1 : (M n).xs ≤ 1:=by
    have H : (M n).xs ≤ W n:=by rw [hcanonical];exact le_max_left _ _
    exact H.trans hw
  intro L us hus hret hmesh
  filter_upwards [hn (M n) hs hxs1 L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U i star seed st hseed hgen hleaf hP hi hs hU x hx hxW hmi hms HK
  exact hj U i star seed st hseed hgen hleaf hP hi hs hU x (W n) hx hxW hmi hms HK

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_constant_deleted_site_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceDeletedSiteOnGivenCutsAlong depth C M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨C,hC,HR⟩:=actual_selected_bad_history_deleted_site_forest_rate_along_comparable_context (c0:=c0)
    0 1 3 depth Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim M G
    W hcanonical hWlim
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  refine ⟨6*C,by positivity,?_⟩
  filter_upwards [HR,Htotal,Hcuts] with n hn ht hcuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,_,Hmass,_,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  refine ⟨Hs,hU,?_⟩
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  let rate:=((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W n*(M n).xs^2)
  have hW : 0 < W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos
  have hrate : 0 ≤ rate:=by dsimp only [rate];positivity
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW.le)
  have Hrow Q (hQ : Q∈nativeActualConstantSourceChildren (M n) as star U Hs hU) :
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) Hs hU (W n) depth [Q]) .deletedSite| ≤
        |Q.term.coefficient| *(C*rate):=by
    have Hvalid:=nativeActualConstantSourceChildren_valid (M n) Hs hU Q hQ
    have Hgen:=nativeActualConstantSourceChildren_generation (M n) Hs hU Q hQ
    have Hleaf:=nativeActualConstantSourceChildren_leaves (M n) Hs hU Q hQ
    have H:=hj U 0 star [] Q (by simp) Hgen Hleaf Hvalid (Nat.zero_le star) Hs hU
      (M n).xs le_rfl (by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale)
      (by simp only [partitionPoint,partitionValues_zero,id_eq];exact mul_nonneg hCm (M n).hxs.le)
      Hmass' HK
    simp only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] at H
    exact H.trans_eq (by dsimp only [rate];ring)
  have H:=actual_constant_deleted_site_category_family_abs_le (M n) ht.1
    (finiteCutMasses_ordered us hus jGrid) Hs hU (W n) (C*rate) depth
    (mul_nonneg hC.le hrate) Hrow
  exact H.trans_eq (by dsimp only [rate];ring)

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 24000000
variable {dim : ℕ → ℕ}

theorem actual_selected_bad_history_constant_longitudinal_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceLongitudinalOnGivenCutsAlong depth C M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_constant_child_longitudinal_category_rate_along_of_pullback_clocks
    dim hdim depth Bclock Temp Cf Cmass Cmass cK hTemp hCf hCm hCm hcK
    (D:=D) (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,Hsource,Hps,Htotal,Hcuts,hcompare,HW] with n hn hs hp ht hcuts hcomp hw
  intro L us hus hret hmesh hstar hhigh houter
  have H:=hn (M n) Temp 
    hs hp ht.1 hcomp (by simpa only [hcanonical n] using hw) L us hus hret hmesh
  filter_upwards [H] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,Houter,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  intro right
  have hW : 0 ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos.le
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW)
  have Hhigh':=(partitionPoint_mono _ (finiteCutMasses_ordered us hus j) HUV.le).trans
    (Houter.trans (mul_le_mul_of_nonneg_right hA hW))
  have HH:=hj _ _ Hs (HUV.le.trans HV)
    (by simpa only [hcanonical n] using Hfirst) (by simpa only [hcanonical n] using Hhigh')
    (by simpa only [hcanonical n] using Hmass') (by simpa only [hcanonical n] using HK) right
  simpa only [hcanonical n,nativeActualFourOtherCategorySum] using HH

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_constant_post_longitudinal_envelope_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK cKcut A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hcKcut : 0 < cKcut) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourcePostLongitudinalEnvelopeAlong depth Temp cK err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  have HR d:=actual_selected_bad_history_constant_longitudinal_on_given_cuts_along_comparable_context (c0:=c0)
    (Ccal:=Ccal) d Cmass hCm hA hcKcut hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin hdim M G
    W radius hcanonical hWlim hcompare w high outer Hcuts
  choose Cd hCd HD using HR
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+Cmass)
  let B:=Real.exp (-4*Temp)*cK
  have hB : 0 < B:=mul_pos (Real.exp_pos _) hcK
  have hR : 0 < R:=by dsimp only [R];positivity
  let save n:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  let err n:=2*((List.range depth).map Cd).sum*(R/B)*save n
  have Hpow:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
    (by norm_num : (0:ℝ)<256))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,save,Function.comp_def,mul_zero] using
      Hpow.const_mul (2*((List.range depth).map Cd).sum*(R/B))
  have HF:=Filter.eventually_all.mpr (fun d : Fin depth=>HD d.val)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨err,Herr,?_⟩
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW] with n hn hclock hsource hcuts hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter
  have Hnet:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,_,Hmass,_,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW.le)
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass') hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_post_Taylor_envelope_longitudinal_paid
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*(Cd d*save n)) (by
      intro d hd right
      obtain ⟨_,_,H⟩:=hj ⟨d,hd⟩
      have H':=H right
      change |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) (nativeActualLongitudinalCategory right)|/
        (chi*K star) ≤ Cd d*save n*(M n).xs^2 at H'
      exact actual_saved_denominator_upper_transfer hden hW hB (mul_nonneg (hCd d).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) Hd H')
  apply Hpaid.trans_eq
  dsimp only [err]
  simp only [List.sum_map_mul_left,List.sum_map_mul_right]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_susceptibility_bound_by_joint_source_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 A : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hA : 0 ≤ A)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
      (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠk : ℕ in atTop,
      ∀(before after : List PositiveMass) (a : PositiveMass),
        before++a::after=finiteCutMasses us k→∀V : ℕ,
        let as:=before++a::after
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=before.length+1
        star < U→U ≤ V→V ≤ as.length→a.val < partitionPoint 0 as V→
        partitionPoint 0 as V ≤ A*W n→
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let S:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |T*chi^2-1| ≤ C*(W n)^2+
          |nativeActualConstantJointStarSource (dim n) as star U b h K S|/
            ((3*(starMassBandConstant cu Az/cu)/4)*W n) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨R,hR,HR⟩:=eventually_actual_selected_bad_history_original_continuum_scalar_remainder_comparable_context
    Bclock T A c0 (by linarith) hA hc0 hm hdelta hroom hcl hcu hAz hC0 hCt
    hmargin hcapmargin dim hdim M G W hxs hWlim
  let c:=starMassBandConstant cu Az/cu
  let Cr:=nativeScalarLowRemainderConstant A R R
  let C:=((c+1)/4+Cr+1)/(3*c/4)
  have hc : 0 < c:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hCr : 0 ≤ Cr:=nativeScalarLowRemainderConstant_nonneg hA hR.le hR.le
  have hC : 0 < C:=by dsimp only [C];positivity
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M
    G
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,Htotal,hw] with n hnR hnTotal hnSharp
  intro us hus hstar
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have HM:=nativeRetainedFinitePhysicalMean_tendsto (dim n) (M n).bf (M n).hf
    (M n).inherited_bf_monotone (M n).inherited_hf_monotone us hus (w n).star hstar
  have Hmean:=HM.eventually (Metric.ball_mem_nhds _ (pow_pos hW 3))
  filter_upwards [Hmean] with k hkMean
  intro before after a hgrid V
  dsimp only
  intro hs hUV hV hbuffer hsize
  let as:=before++a::after
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=before.length+1
  have ho : MassOrdered 0 as:=by
    dsimp only [as]
    rw [hgrid]
    exact finiteCutMasses_ordered us hus k
  have hstar' : (w n).star∈as:=by
    dsimp only [as]
    rw [hgrid]
    exact finiteCutMasses_nodes us k hstar
  have Hscalar:=hnR before after a ho star V hs hUV hV hbuffer hsize
    (ClockTree.single (S:=Spin (dim n)×Bool) as) 0 ho (singleSlot as)
  dsimp only at Hscalar
  rw [native_full_gamma_row_hessian (dim n) (ClockTree.single (S:=Spin (dim n)×Bool) as)
    ho 0 ho U (by dsimp [U];omega)] at Hscalar
  have Hmesh : |finitePhysicalMean (dim n+1) as
      (fun j=>((M n).bf (partitionPoint 0 as j):ℝ))
      (fun j=>((M n).hf (partitionPoint 0 as j):ℝ)) star-
      orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val| ≤ (W n)^3 := by
    dsimp only [as,star]
    rw [hgrid]
    exact (show |_ - _| < (W n)^3 by simpa only [Metric.mem_ball,Real.dist_eq] using hkMean).le
  exact actual_sharp_susceptibility_bound_by_joint_source (M n) hcu hAz hW hnTotal.1
    (w n) hnSharp as ho hstar' U hs (hUV.trans hV) Hmesh Hscalar

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem actual_selected_bad_history_susceptibility_on_source_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 A cFirst cK : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hA : 0 ≤ A)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n))
    (high outer : ℕ→PositiveMass) (radius : ℕ→ℝ)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
      (∀u∈us,u.val ≤ 1)→(w n).star∈us→(high n)∈us→(outer n)∈us→∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex (high n).val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let S:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |T*chi^2-1| ≤ C*(W n)^2+
          |nativeActualConstantJointStarSource (dim n) as star U b h K S|/
            ((3*(starMassBandConstant cu Az/cu)/4)*W n) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨C,hC,HC⟩:=actual_selected_bad_history_susceptibility_bound_by_joint_source_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hA hmargin hcapmargin
    dim hdim M G W hxs hWlim w hw
  refine ⟨C,hC,?_⟩
  filter_upwards [HC,Hcuts] with n hnC hnCuts
  intro us hus hstar hhigh houter
  filter_upwards [hnC us hus hstar] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  let V:=retainedMassPrefixIndex (outer n).val as
  obtain ⟨hs,hUV,hV,_,_,hcap,_,_,_,_,_,_,before,after,hgrid,hindex⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter k
  have Hbuffer : (high n).val < partitionPoint 0 as V:=by
    rw [nativeRetainedCut_partitionPoint as (finiteCutMasses_ordered us hus k)
      (outer n) (finiteCutMasses_nodes us k houter)]
    exact hnCuts.high_lt
  have H:=hk before after (high n) hgrid.symm V
  rw [←hgrid,hindex] at H
  exact H hs hUV.le hV Hbuffer hcap

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_susceptibility_by_other_sources_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Cwindow c0 A cFirst cKcut cK gamma sharpSaving terminalSaving : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0≤1) (hA : 0≤A)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hcK : 0 < cK) (hgamma : 0≤gamma) (hsharp : 0 < sharpSaving) (hterminal : 0≤terminalSaving)
    (depth : ℕ) (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (high outer : ℕ → PositiveMass) (radius : ℕ → ℝ)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK gamma sharpSaving terminalSaving depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
      (∀u∈us,u.val≤1) → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
        let as:=finiteCutMasses us j
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex (high n).val as
        ∃hs : star < U,∃hU : U≤as.length,
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        let cS:=3*(starMassBandConstant cu Az/cu)/4
        |T*chi^2-1|≤C*(W n)^2+
          2*((T/cS)*nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth+
            |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  have hTemp : 0 < T := G.hT
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cs,hCs,Hsus⟩:=actual_selected_bad_history_susceptibility_on_source_cuts_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hA hmargin hcapmargin
    dim hdim M G W hxs hWlim w hw high outer radius Hcuts
  obtain ⟨Cb,hCb,Hbond⟩:=actual_selected_bad_history_susceptibility_coefficient_along_comparable_context (c0:=c0)
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim w hw
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  let coefficient:=(T/cS)*(6*(depth:ℝ)/(Real.exp (-4*T)*cK))
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have Hpow : Tendsto (fun n=>((dim n+1:ℕ):ℝ)^(-sharpSaving/2)) atTop (𝓝 0):=by
    convert (tendsto_rpow_neg_atTop (half_pos hsharp)).comp HN using 1
    funext n
    simp only [Function.comp_apply,neg_div]
  have Hsmall : ∀ᶠn in atTop,coefficient*((dim n+1:ℕ):ℝ)^(-sharpSaving/2)≤1/2:=by
    have H:=Hpow.const_mul coefficient
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2))
  let C:=2*(Cs+(T/cS)*(6*(depth:ℝ)+13)+Cb)+1
  have hT : 0≤T:=by linarith
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsus,Hbond,Htotal,Hknown,Hcuts,Hsmall] with n hnS hnB hnT hnKnown hnCuts hnSmall
  intro us hus hstar hhigh houter
  filter_upwards [hnS us hus hstar hhigh houter,hnKnown us hus hstar] with j hjS hjKnown
  dsimp only at hjS hjKnown ⊢
  obtain ⟨hs,hUV,hV,_⟩:=hnCuts.finite_net_readout us hus hstar hhigh houter j
  have hU:=hUV.le.trans hV
  refine ⟨hs,hU,?_⟩
  have ho:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have H:=actual_minimum_constant_source_susceptibility_feedback_absorption (M n) hs hU ho hnT.1
    hW (hxs n) hcK hcS hgamma hterminal depth (hjKnown _ hs hU) hjS
    (hnB _ ho (finiteCutMasses_nodes us j hstar) _ hs hU) hnSmall
  apply H.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have HB:=mul_le_mul_of_nonneg_right hnSmall hCb.le
  dsimp only [C,coefficient,cS] at HB ⊢
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem exists_actual_selected_bad_history_constant_source_known_envelope_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0<saving ∧ 0<sharpSaving ∧∃cK : ℝ,0<cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0≤Cf ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0<Cs ∧∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0<degree→
        ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenPairLevelSavingAlong depth saving sharpSaving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong depth saving M W w) ∧
      ActualOriginalConstantSourceChildrenFrozenSavingAlong saving M W w ∧
      ∃threshold : ℕ,0<threshold ∧∃terminalSaving : ℝ,0<terminalSaving ∧
        ∀depth : ℕ,threshold≤depth→
          ActualOriginalConstantSourceChildrenFourTerminalSavingAlong depth terminalSaving M W w ∧
          ActualConstantSourceKnownEnvelopeAlong T cK saving sharpSaving terminalSaving depth M W w := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,Cs,hCs,w,hw,HK,Hsquare,Hmixed,Hconstant,
    Hpair,Hfrozen,Hinitial,threshold,hthreshold,tau,htau,Hterm⟩:=
    exists_actual_selected_bad_history_constant_source_four_inputs_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,Cs,hCs,w,hw,HK,Hsquare,Hmixed,Hconstant,
    Hpair,Hfrozen,Hinitial,threshold,hthreshold,tau,htau,?_⟩
  intro depth hd
  refine ⟨Hterm depth hd,?_⟩
  exact actual_constant_source_known_envelope_along hcK depth M W hxs
    (Htotal.mono (fun _ hn=>hn.1)) w HK
    (fun j _=>Hpair j) (fun j _=>Hfrozen j) Hinitial (Hterm depth hd)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem exists_actual_selected_bad_history_susceptibility_bootstrap_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
        (∀u∈us,u.val≤1) → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨hsaving,hsharp,cK,hcK,_Htotal,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,_HK,Hsquare,Hmixed,Hconstant,
    _Hpair,_Hfrozen,_Hinitial,threshold,hthreshold,tau,htau,Hknown⟩:=
    exists_actual_selected_bad_history_constant_source_known_envelope_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts⟩:=
    exists_actual_sharp_source_cuts_along hcl hcu hAz hTemp hL M W hxs hWlim w hw
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  exact actual_selected_bad_history_susceptibility_by_other_sources_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hc0 hc01 (by linarith : 0≤Ku+1)
    hmargin hcapmargin hgapmargin hcK hsaving.le hsharp htau.le depth
    dim hdim M G W hcanonical hWlim
    w hw high outer (fun n=>Kv*W n) Hcuts (Hknown depth hd).2

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 30000000
variable {dim : ℕ → ℕ}

theorem actual_selected_bad_history_constant_source_category_envelope_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cKcut cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (hA : A ≤ Cmass)
    (hcKcut : 0 < cKcut) (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (heta : 0 < eta) (hgap : 2*eta < 6*m)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ → ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceCategoryEnvelopeAlong depth Temp cK
      (min eta (actualMassSavingExponent m delta/256)) C M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  have Hrates d : ∃Cg Cr Cf : ℝ,0 < Cg ∧ 0 < Cr ∧ 0 < Cf ∧
      ActualConstantSourceGaCurrentOnGivenCutsAlong d eta Cg M W w high outer ∧
      ActualConstantSourceGaRestorationOnGivenCutsAlong d Cr M W w high outer ∧
      ActualConstantSourceFirstHighOnGivenCutsAlong d Cf M W w high outer:=by
    obtain ⟨Cg,Cf,hCg,hCf,HG,HF⟩:=actual_selected_bad_history_constant_source_rates_on_given_cuts_along_comparable_context (c0:=c0)
      d Cmass hCm hA hcKcut hc hcouter heta hgap hm hdelta hroom hcl hcu hAz hC0 hCt
      hCcal hc0 hmargin hcapmargin hdim M G
      W radius hcanonical hWlim hcompare saving hsaving w Hmixed high outer Hcuts
    obtain ⟨Cr,hCr,HR⟩:=actual_selected_bad_history_constant_source_restoration_on_given_cuts_along_comparable_context (c0:=c0)
      d Cmass (zero_le_one.trans hCm) hA hcKcut hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt
      hc0 hmargin hcapmargin hdim M G
      W radius hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
    exact ⟨Cg,Cr,Cf,hCg,hCr,hCf,HG,HR,HF⟩
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have hxs n : (M n).xs ≤ W n:=
    (M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  have Hupper : ∀ᶠn in atTop,actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val ≤
      (CK*(1+Cmass))*W n:=by
    filter_upwards [hdim.eventually HK,Hsource,Hcuts] with n hn hs hcuts
    have hu : (w n).star.val∈Icc (0:ℝ) 1:=
      ⟨(w n).star.property.le,hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_le_one)⟩
    have hW : 0 ≤ W n:=((M n).hxs.trans_le (hxs n)).le
    have Hmass : (w n).star.val ≤ Cmass*W n:=
      (hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_scale)).trans
        (mul_le_mul_of_nonneg_right hA hW)
    have Hsize : (M n).xs+(w n).star.val ≤ (1+Cmass)*W n:=by linarith [hxs n]
    exact (hn (M n) hs _ hu).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hsize hCK.le)
  exact actual_constant_source_category_envelope_along_of_closed_rates depth heta hm hdelta hcK hcKcut
    (mul_pos hCK (by linarith)) hdim M W radius hxs w high outer
    (Htotal.mono (fun _ h=>h.1)) Hupper Hcuts Hrates

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000

theorem exists_actual_selected_bad_history_susceptibility_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_bootstrap_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hfactor : 0 ≤ T/cS:=div_nonneg hT.le hcS.le
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hsaving : 0 ≤ actualSlowWindowExponent m delta/256:=
    (div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)).le
  let rho:=min m (actualMassSavingExponent m delta/256)
  have hrho : 0 ≤ rho:=le_min hm.le (div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num))
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨Ce,hCe,HE⟩:=actual_selected_bad_history_constant_source_category_envelope_along_comparable_context (c0:=c0)
    (eta:=m) depth (Ku+1) (by linarith) le_rfl hcKcut hcK hFirst hFirstLower hm (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin hdim
    M G W (fun n=>Kv*W n)
    hcanonical hWlim hcompare (actualSlowWindowExponent m delta/256) hsaving w Hmixed high outer Hcuts
  let C:=Cb+2*(T/cS)*Ce
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,HE] with n hnB hnE
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB us hus hstar hhigh houter,hnE Lnet us hus hret hmesh hstar hhigh houter]
    with j hjB hjE
  dsimp only at hjB hjE ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HE⟩:=hjE
  refine ⟨hs,hU,?_⟩
  let N:=((dim n+1:ℕ):ℝ)
  have hN : 1 ≤ N:=by dsimp only [N];exact_mod_cast (show 1 ≤ dim n+1 by omega)
  have hpow : N^(-rho) ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hrho)
  have hxs2 : (M n).xs^2 ≤ (W n)^2:=by nlinarith [(M n).hxs,hxs n]
  have Hrate : Ce*N^(-rho)*(M n).xs^2 ≤ Ce*(W n)^2:=by
    have H:=(mul_le_mul_of_nonneg_right hpow (sq_nonneg (M n).xs)).trans (by simpa using hxs2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H hCe.le
  have HE' : nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth ≤
      Ce*(W n)^2+nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth:=
    HE.trans (add_le_add Hrate le_rfl)
  have HH:=mul_le_mul_of_nonneg_left HE' hfactor
  dsimp only [C,cS] at HH ⊢
  nlinarith only [HB,HH]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000

theorem actual_selected_bad_history_constant_source_remainder_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (hA : 0 ≤ A) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
        let as:=finiteCutMasses us j
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex (high n).val as
        |nativeActualConstantSourceRemainder (M n) as star U| ≤ C*W n*(M n).xs^2+
          |nativeActualConstantSourceTaylorPart (M n) as star U| := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  obtain ⟨CL,hCL,HR⟩:=eventually_actual_shell_history_retained_constant_longitudinal_rate_along_of_pullback_clocks
    dim hdim 2 Bclock Temp Cf A hTemp hCf hA
    (D:=D) (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have Homit:=hdim.eventually (eventually_actual_omitted_product_cubic_cost_saved
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 (2*Temp) (by positivity))
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  let C:=2*CK*(1+A)*(1+CL)+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,hdim.eventually HK,Hsource,Hps,Htotal,Hcuts,hcompare,HW,Homit]
    with n hnL hnK hs hp ht hcuts hcomp hw hnOmit
  intro L us hus hret hmesh hstar hhigh houter
  have hxs : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxs
  have hxs1 : (M n).xs ≤ 1:=hxs.trans hw
  have H:=hnL (M n) 
    hs hp ht.1 ht.2 hcomp (by simpa only [hcanonical n] using hw) L us hus hret hmesh
  have HM:=eventually_native_finite_physical_mean_uniform_center (dim n) (M n).bf (M n).hf
    (M n).inherited_bf_monotone (M n).inherited_hf_monotone ((M n).inherited_zero_root_field ht.2)
    us hus (1/(dim n+1:ℕ)) (by positivity)
  filter_upwards [H,HM] with j hj hjM
  dsimp only at hj hjM ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  let g:=nativeFreshAtSlot (ClockTree.single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) star
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,Houter,_,_,_,_,_,_,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  have hU:=HUV.le.trans HV
  have Hhigh:=(partitionPoint_mono as ho HUV.le).trans Houter
  have Hleaves : g.tree.leaves ≤ 2:=by
    have Hleaf:=(ClockTree.single (S:=Spin (dim n)×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem _ 0 (singleSlot as) star)
    simpa only [single_leaves_exact] using Hleaf
  have HL:=hj U g.tree hU Hleaves (by simpa only [hcanonical n] using Hfirst)
    (by simpa only [hcanonical n] using Hhigh)
    (native_constant_calibration_fresh_tree_HIGH_fork_free as star U Hs)
  have Hclock : nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star ≤ CK*(1+A)*W n:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    have Hc:=hnK (M n) hs (w n).star.val
      ⟨(w n).star.property.le,hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_le_one)⟩
    have Hmass':(w n).star.val ≤ A*W n:=
      hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_scale)
    nlinarith only [Hc,hCK,hxs,Hmass']
  have Hret:=actual_constant_source_retained_part_abs_le (M n)
    (E:=((M n).context.N^(-(1:ℝ)/3)+CL*(M n).context.N^(-(actualMassSavingExponent m delta/256)))*(M n).xs^2)
    ht.1 as ho star U Hs hU Hclock HL
  have Hmean:=actual_constant_source_mean_part_abs_le (M n) ht.1 as ho star U Hs hU
    (hjM star (Hs.le.trans hU))
  have hN : 1 ≤ (M n).context.N:=by change (1:ℝ) ≤ (dim n+1:ℕ);exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have H1:=Real.rpow_le_one_of_one_le_of_nonpos hN (show -(1:ℝ)/3 ≤ 0 by norm_num)
  have H2:=Real.rpow_le_one_of_one_le_of_nonpos hN
    (show -(actualMassSavingExponent m delta/256) ≤ 0 by linarith [actualMassSavingExponent_pos hm hdelta])
  have Hret' : |nativeActualConstantSourceRetainedPart (M n) as star U| ≤
      2*CK*(1+A)*(1+CL)*W n*(M n).xs^2:=by
    apply Hret.trans
    have HE : (M n).context.N^(-(1:ℝ)/3)+CL*(M n).context.N^(-(actualMassSavingExponent m delta/256)) ≤ 1+CL:=by
      nlinarith
    have HH:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right HE (sq_nonneg (M n).xs))
      (show 0 ≤ 2*(CK*(1+A)*W n) by positivity)
    convert HH using 1
    ring
  have HO:=hnOmit (M n) (W n) hxs
  have H6:=Real.rpow_le_one_of_one_le_of_nonpos hN (show -(1:ℝ)/6 ≤ 0 by norm_num)
  have HO' : 2*Temp/(dim n+1:ℕ) ≤ W n*(M n).xs^2:=by
    have Hden : (dim n+1:ℕ)*(M n).xs ≤ (dim n+1:ℕ)*(1:ℝ):=
      mul_le_mul_of_nonneg_left hxs1 (by positivity)
    have Hdiv:=div_le_div_of_nonneg_left (show 0 ≤ 2*Temp by positivity)
      (show 0 < (dim n+1:ℕ)*(M n).xs by have :=(M n).hxs;positivity) Hden
    simp only [mul_one] at Hdiv
    apply Hdiv.trans (HO.trans _)
    change (M n).context.N^(-(1:ℝ)/6)*(W n*(M n).xs^2) ≤ _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right H6 (by positivity : 0 ≤ W n*(M n).xs^2)
  rw [nativeActualConstantSourceRemainder_eq_parts]
  have Habs:=(abs_add_le
    (nativeActualConstantSourceRetainedPart (M n) as star U+nativeActualConstantSourceMeanPart (M n) as star U)
    (nativeActualConstantSourceTaylorPart (M n) as star U)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  dsimp only [C]
  nlinarith only [Habs,Hret',Hmean,HO']

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000

theorem exists_actual_selected_bad_history_susceptibility_taylor_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceTaylorPart (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_categories_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cr,hCr,HR⟩:=actual_selected_bad_history_constant_source_remainder_on_given_cuts_along_comparable_context (c0:=c0)
    (by linarith : 0 ≤ Ku+1) hFirst hFirstLower hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim M G
    W (fun n=>Kv*W n) hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  refine ⟨Cb+2*Cr/cS,by positivity,?_⟩
  filter_upwards [HB,HR] with n hnB hnR
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnR Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjR
  dsimp only at hjB hjR ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  refine ⟨hs,hU,?_⟩
  exact susceptibility_bootstrap_remainder_reduction
    ((M n).hxs.trans_le (hxs n)) hcS (M n).hxs.le (hxs n) hCr.le HB hjR

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_constant_pending_category_envelope_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 cFirst cKcut cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcKcut : 0 < cKcut) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourcePendingCategoryEnvelopeAlong depth Temp cK C M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  apply actual_constant_pending_category_envelope_along_of_deleted_rates depth hcK M W radius
    (by intro n;rw [hcanonical];exact (M n).canonical_direct_test_band_pos) w high outer Hcuts
  intro d
  exact actual_selected_bad_history_constant_deleted_site_on_given_cuts_along_comparable_context (c0:=c0)
    d Cmass hCm hA hcKcut hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin
    hdim M G W radius hcanonical hWlim w high outer Hcuts

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 30000000

theorem actual_second_low_actual_history_constant_B0_vanishing_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Ccompare c0 : ℝ}
    (Couter : ℝ) (hTemp : 0 ≤ Temp) (hCouter : 0 ≤ Couter) (hCompare : 0 ≤ Ccompare)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃eps : ℕ → ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualSecondLowOriginalConstantB0AmplitudeBoundOnEveryFinalNetAlong Couter eps M W w := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  obtain ⟨C,hC,HB⟩:=actual_second_low_original_constant_B0_budget_along Couter hTemp hCf hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource hw
  let eps:=fun n=>actualSecondLowOriginalConstantB0Amplitude (M n) Temp Cf Couter C
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE]
    exact hWlim
  refine ⟨eps,?_,actual_second_low_inherited_constant_B0_amplitude_tendsto_zero_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hCouter dim hdim M G hsmall HL,?_⟩
  · intro n
    have HS:0 < (M n).actualOriginalLowErrorDensitySaving (Couter+1):=
      (M n).actualOriginalLowErrorDensitySaving_pos (by linarith)
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    dsimp [eps,actualSecondLowOriginalConstantB0Amplitude]
    positivity
  · filter_upwards [HB] with n hn
    intro L us hus hstar hret hmesh
    filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
    dsimp only at hgrid ⊢
    intro U hU hstarU houter
    have H:=hgrid U hU hstarU houter
    let as:=finiteCutMasses us jGrid
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hx:0 < (M n).xs:=(M n).hxs
    have hW:0 ≤ W n:=hx.le.trans ((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm)
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    have Hrho:(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
        partitionPoint 0 as U/(dim n+1:ℕ) ≤
        ((M n).actualOriginalLowErrorDensitySaving (Couter+1)+(1/(dim n+1:ℕ):ℝ)/(M n).xs^2)*(M n).xs^2:=by
      rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (partitionPoint_mem as ho U).2 (by positivity))
    apply H.trans
    have HH:=add_le_add_left (mul_le_mul_of_nonneg_left Hrho (mul_nonneg (mul_nonneg hC.le hW) HCerr))
      (16*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2)
    convert HH using 1 <;> (try dsimp [eps,actualSecondLowOriginalConstantB0Amplitude]) <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000

theorem actual_selected_bad_history_constant_joint_Taylor_rate_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Ccompare c0 c : ℝ}
    (Ccut : ℝ) (hTemp : 0≤Temp) (hCcut : 0 < Ccut) (hCompare : 0≤Ccompare)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hc0 : 0 < c0) (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c)
    (hmargin : delta/4<3*m-99*delta) (hcapmargin : 100*delta<(1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧ ∀ᶠn : ℕ in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (w n).star∈us →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) star
        ∀U : ℕ,star<U → U≤as.length → 2*c*W n≤partitionPoint 0 as U →
          partitionPoint 0 as U≤ min (Ccut*W n) 1 →
          |nativeActualJointRestoredForwardTaylorError (dim n) q U b h K S g.tree (fun _=>1)
            (g.embed (singleSlot as)) g.mark|≤err n*(W n*(M n).xs^2) := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Hshell := G.pullback
  obtain ⟨eT,heT,HT⟩:=actual_inherited_constant_fresh_full_Taylor_rate_along_of_pullback_clocks
    (Cs:=Ccompare) (Cwindow:=Cs) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hc hcouter dim hdim
    M W hcanonical hWlim Hsource hsmall Hshell w hw
  obtain ⟨C2,hC2,H2⟩:=eventually_actual_shell_history_constant_fresh_C_two_HIGH_rate_along_of_pullback_clocks
    (Cs:=Ccompare) dim hdim Bclock Temp Cf Ccut hTemp hCf hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hc hcouter
  obtain ⟨C4,hC4,H4⟩:=eventually_actual_shell_history_constant_fresh_FOUR_G_LOW_rate_along_of_pullback_clocks
    (Cs:=Ccompare) dim hdim Bclock Temp Cf Ccut hTemp hCf hCcut.le
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hc hcouter
  have HL:=actual_inherited_constant_low_restoration_star_rate_along
    2 Bclock Temp Cf Ccut hTemp hCf hCcut.le hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim Hsource w hw
  obtain ⟨eB,heB0,heB,HB⟩:=actual_second_low_actual_history_constant_B0_vanishing_along_comparable_context (c0:=c0)
    Ccut hTemp hCcut.le hCompare hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin
    dim hdim M G W hcanonical hWlim w hw hsmall
  let eta:=actualMassSavingExponent m delta
  let err:=fun n=>eB n+|eT n|+(C2+C4)*((dim n+1:ℕ):ℝ)^(-eta/256)+((dim n+1:ℕ):ℝ)^(-eta/32)
  have Hpow (d : ℝ) (hd : 0 < d) :=(tendsto_rpow_neg_atTop (div_pos
    (actualMassSavingExponent_pos hm hdelta) hd)).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    have H:=((heB.add heT.abs).add ((Hpow 256 (by norm_num)).const_mul (C2+C4))).add
      (Hpow 32 (by norm_num))
    simpa only [err,eta,Function.comp_def,abs_zero,zero_mul,mul_zero,add_zero,neg_div] using H
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HT,H2,H4,HL,HB,Hsource,Hshell,hsmall,HW1] with n hnT hn2 hn4 hnL hnB hnSource hnShell hnSmall hnW
  have hb' := hnShell
  have hW1 : (M n).canonicalDirectTestBandScale≤1:=by simpa only [←hcanonical] using hnW
  have hxW : (M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  intro L us hus hstar hret hmesh
  filter_upwards [hnT L us hus hret hmesh hstar,
    hn2 (M n)  hnSource hb' hnSmall hW1 L us hus hret hmesh,
    hn4 (M n)  hnSource hb' hnSmall hW1 L us hus hret hmesh,
    hnL L us hus hret hmesh hstar,hnB L us hus hstar hret hmesh]
      with jGrid hgridT hgrid2 hgrid4 hgridL hgridB
  dsimp only at hgridT hgrid2 hgrid4 hgridL hgridB ⊢
  intro U hs hU hcutlo hcut
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let T:=single (S:=Spin (dim n)×Bool) as
  let s : T.Slot:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves≤2:=by
    have H:=T.markedAttach_leaves 0 _ (nativeFreshAtSlot_mem T 0 s star)
    simpa only [T,g,single_leaves_exact] using H
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hU)]
  have haz : g.tree.splitIndex (g.embed s) g.mark<U:=hsplit.trans_lt hs
  have HTay:=hgridT U hs hU hcutlo hcut 0 (g.embed s) g.mark
  have HC2:=hgrid2 star U hs hU (by simpa only [←hcanonical] using hcutlo)
    (by simpa only [←hcanonical] using hcut.trans (min_le_left _ _)) 0 (g.embed s) g.mark haz
  have HC4:=hgrid4 star U hs hU (by simpa only [←hcanonical] using hcutlo)
    (by simpa only [←hcanonical] using hcut.trans (min_le_left _ _)) 0 (g.embed s) g.mark
  have HCL:=hgridL U g.tree hU hg (hcut.trans (min_le_left _ _)) (g.embed s) g.mark hsplit hs
  have HB0:=hgridB U hU hs (hcut.trans (min_le_left _ _))
  have HBsource : (1/2:ℝ)*nativeRetainedCenteredCoefficient (dim n) q U b h K g.tree
      (fun _=>1) [g.embed s,g.mark] 2 0=
      nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed s,g.mark]/2:=by
    rw [native_second_low_centered_eq_scalar_subtraction (dim n) q U b h K g.tree ho (fun _=>1)
      (g.embed s) g.mark hU haz,←native_second_low_joint_ledger_eq_scalar_subtraction
        (dim n) q U b h K g.tree ho (fun _=>1) [g.embed s,g.mark]]
    ring
  have hprice : 0≤W n*(M n).xs^2:=mul_nonneg ((M n).hxs.trans_le hxW).le (sq_nonneg _)
  have HTay' :=HTay.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hprice)
  have Habs : |nativeActualJointRestoredForwardTaylorError (dim n) q U b h K S g.tree (fun _=>1)
      (g.embed s) g.mark|≤
      |nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed s,g.mark]/2|+
      |nativeActualTaylorRemainder (dim n) q U b h K g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeCenteredLowGammaHighSecondRemainder (dim n) q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeCenteredLowGammaLowRestoration (dim n) q U b h K S g.tree (fun _=>1) (g.embed s) g.mark|+
      |nativeOriginalGKernelLowRestoration (dim n) q U b h K S g.tree (fun _=>1) (g.embed s) g.mark
        (restCenteredLowKernel (dim n) U b S)|:=by
    unfold nativeActualJointRestoredForwardTaylorError nativeActualHigherAllocatedRemainder
    rw [HBsource]
    exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  have Htotal:=add_le_add (add_le_add (add_le_add (add_le_add HB0 HTay') HC2) HCL) HC4
  apply Habs.trans (Htotal.trans_eq _)
  dsimp only [err,eta]
  simp only [NativeOverlapContext.N,←hcanonical,neg_div]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_pending_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePendingCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_taylor_categories_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨err,herr,HTaylor⟩:=actual_selected_bad_history_constant_joint_Taylor_rate_along_comparable_context (c0:=c0)
    (Ccompare:=Ccal^2) (Ku+1) hT.le (by linarith) (sq_nonneg Ccal)
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hFirst hFirstLower hmargin hcapmargin
    dim hdim M G W hcanonical hWlim w hw
    (Filter.Eventually.of_forall hcompare)
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨Cd,hCd,HD⟩:=actual_selected_bad_history_constant_pending_category_envelope_along_comparable_context (c0:=c0)
    depth (Ku+1) (by linarith) le_rfl hcKcut hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin hdim M G
    W (fun n=>Kv*W n) hcanonical hWlim w high outer Hcuts
  refine ⟨Cb+2*(T/cS)*Cd+2/cS,by positivity,?_⟩
  filter_upwards [HB,HD,HTaylor,Herr,Hcuts] with n hnB hnD hnT hne hnCuts
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnD Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hstar hret hmesh] with j hjB hjD hjT
  dsimp only at hjB hjD hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HD⟩:=hjD
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  obtain ⟨_,HUV,HV,Hlo,_,Houter,_,_,_,_,_,_,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  have Hupper : partitionPoint 0 as U≤ min ((Ku+1)*W n) 1:=by
    refine le_min ?_ (partitionPoint_mem as ho U).2
    exact (partitionPoint_mono as ho HUV.le).trans Houter
  have HT:=hjT U hs hU Hlo Hupper
  have HS : (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k))=
      nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as:=by
    funext k
    exact native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone (partitionPoint_mem as ho k)
  change |nativeActualJointRestoredForwardTaylorError (dim n) _ U _ _ _
    (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k)) _ _ _ _|≤_ at HT
  rw [HS] at HT
  change |nativeActualConstantSourceTaylorPart (M n) as star U|≤err n*(W n*(M n).xs^2) at HT
  have HT' : |nativeActualConstantSourceTaylorPart (M n) as star U|≤W n*(M n).xs^2:=
    HT.trans ((mul_le_mul_of_nonneg_right hne (mul_nonneg (hW n).le (sq_nonneg _))).trans_eq (one_mul _))
  have Hpow : ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dim n)))
      (by norm_num)
  have Hrate : Cd*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2≤Cd*(W n)^2:=by
    have H1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow hCd.le) (sq_nonneg (M n).xs)
    simp only [mul_one] at H1
    exact H1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (M n).hxs.le (hxs n) 2) hCd.le)
  have HD':=HD.trans (add_le_add Hrate le_rfl)
  refine ⟨hs,hU,?_⟩
  exact susceptibility_pending_envelope_absorption (hW n) hcS hT.le (M n).hxs.le (hxs n)
    hCd.le HB HD' HT'

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_post_Taylor_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePostTaylorCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_pending_categories_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hps := G.pullback
  have Hshell := G.pullback
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_post_Taylor_envelope_along_of_pullback_clocks
    depth Bclock T Cf (Ku+1) cK cKcut hT.le hCf (by linarith) hcK hcKcut
    (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hFirst hFirstLower
    dim hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource
    (Filter.Eventually.of_forall hcompare) Hshell w high outer hw Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_post_longitudinal_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePostLongitudinalCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_post_Taylor_categories_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_selected_bad_history_constant_post_longitudinal_envelope_along_comparable_context (c0:=c0)
    (Ccal:=Ccal) depth (Ku+1) (by linarith) le_rfl hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin hdim M
    G W (fun n=>Kv*W n) hcanonical hWlim
    (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_three_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourceThreeCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_post_longitudinal_categories_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_three_category_envelope_along_of_pullback_clocks
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell (actualSlowWindowExponent m delta/256)
    (div_nonneg (actualSlowWindowExponent_pos hm hdelta hroom).le (by norm_num)) w high outer hw Hmixed Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_bootstrap_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
        (∀u∈us,u.val≤1) → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨hsaving,hsharp,cK,hcK,_Htotal,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,_HK,Hsquare,Hmixed,Hconstant,
    _Hpair,_Hfrozen,_Hinitial,threshold,hthreshold,tau,htau,Hknown⟩:=
    exists_actual_selected_bad_history_constant_source_known_envelope_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong⟩:=
    exists_actual_strong_sharp_source_cuts_along Rmacro Cx hmacro hCx hcl hcu hAz hTemp hL M W hxs hWlim w hw
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  exact actual_selected_bad_history_susceptibility_by_other_sources_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hc0 hc01 (by linarith : 0≤Ku+1)
    hmargin hcapmargin hgapmargin hcK hsaving.le hsharp htau.le depth
    dim hdim M G W hcanonical hWlim
    w hw high outer (fun n=>Kv*W n) Hcuts (Hknown depth hd).2

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_bootstrap_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hfactor : 0 ≤ T/cS:=div_nonneg hT.le hcS.le
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hsaving : 0 ≤ actualSlowWindowExponent m delta/256:=
    (div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)).le
  let rho:=min m (actualMassSavingExponent m delta/256)
  have hrho : 0 ≤ rho:=le_min hm.le (div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num))
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨Ce,hCe,HE⟩:=actual_selected_bad_history_constant_source_category_envelope_along_comparable_context (c0:=c0)
    (eta:=m) depth (Ku+1) (by linarith) le_rfl hcKcut hcK hFirst hFirstLower hm (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin hdim
    M G W (fun n=>Kv*W n)
    hcanonical hWlim hcompare (actualSlowWindowExponent m delta/256) hsaving w Hmixed high outer Hcuts
  let C:=Cb+2*(T/cS)*Ce
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,HE] with n hnB hnE
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB us hus hstar hhigh houter,hnE Lnet us hus hret hmesh hstar hhigh houter]
    with j hjB hjE
  dsimp only at hjB hjE ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HE⟩:=hjE
  refine ⟨hs,hU,?_⟩
  let N:=((dim n+1:ℕ):ℝ)
  have hN : 1 ≤ N:=by dsimp only [N];exact_mod_cast (show 1 ≤ dim n+1 by omega)
  have hpow : N^(-rho) ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hrho)
  have hxs2 : (M n).xs^2 ≤ (W n)^2:=by nlinarith [(M n).hxs,hxs n]
  have Hrate : Ce*N^(-rho)*(M n).xs^2 ≤ Ce*(W n)^2:=by
    have H:=(mul_le_mul_of_nonneg_right hpow (sq_nonneg (M n).xs)).trans (by simpa using hxs2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H hCe.le
  have HE' : nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth ≤
      Ce*(W n)^2+nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth:=
    HE.trans (add_le_add Hrate le_rfl)
  have HH:=mul_le_mul_of_nonneg_left HE' hfactor
  dsimp only [C,cS] at HH ⊢
  nlinarith only [HB,HH]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_taylor_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceTaylorPart (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cr,hCr,HR⟩:=actual_selected_bad_history_constant_source_remainder_on_given_cuts_along_comparable_context (c0:=c0)
    (by linarith : 0 ≤ Ku+1) hFirst hFirstLower hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim M G
    W (fun n=>Kv*W n) hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  refine ⟨Cb+2*Cr/cS,by positivity,?_⟩
  filter_upwards [HB,HR] with n hnB hnR
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnR Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjR
  dsimp only at hjB hjR ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  refine ⟨hs,hU,?_⟩
  exact susceptibility_bootstrap_remainder_reduction
    ((M n).hxs.trans_le (hxs n)) hcS (M n).hxs.le (hxs n) hCr.le HB hjR

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_pending_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePendingCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_taylor_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨err,herr,HTaylor⟩:=actual_selected_bad_history_constant_joint_Taylor_rate_along_comparable_context (c0:=c0)
    (Ccompare:=Ccal^2) (Ku+1) hT.le (by linarith) (sq_nonneg Ccal)
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hFirst hFirstLower hmargin hcapmargin
    dim hdim M G W hcanonical hWlim w hw
    (Filter.Eventually.of_forall hcompare)
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨Cd,hCd,HD⟩:=actual_selected_bad_history_constant_pending_category_envelope_along_comparable_context (c0:=c0)
    depth (Ku+1) (by linarith) le_rfl hcKcut hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin hdim M G
    W (fun n=>Kv*W n) hcanonical hWlim w high outer Hcuts
  refine ⟨Cb+2*(T/cS)*Cd+2/cS,by positivity,?_⟩
  filter_upwards [HB,HD,HTaylor,Herr,Hcuts] with n hnB hnD hnT hne hnCuts
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnD Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hstar hret hmesh] with j hjB hjD hjT
  dsimp only at hjB hjD hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HD⟩:=hjD
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  obtain ⟨_,HUV,HV,Hlo,_,Houter,_,_,_,_,_,_,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  have Hupper : partitionPoint 0 as U≤ min ((Ku+1)*W n) 1:=by
    refine le_min ?_ (partitionPoint_mem as ho U).2
    exact (partitionPoint_mono as ho HUV.le).trans Houter
  have HT:=hjT U hs hU Hlo Hupper
  have HS : (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k))=
      nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as:=by
    funext k
    exact native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone (partitionPoint_mem as ho k)
  change |nativeActualJointRestoredForwardTaylorError (dim n) _ U _ _ _
    (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k)) _ _ _ _|≤_ at HT
  rw [HS] at HT
  change |nativeActualConstantSourceTaylorPart (M n) as star U|≤err n*(W n*(M n).xs^2) at HT
  have HT' : |nativeActualConstantSourceTaylorPart (M n) as star U|≤W n*(M n).xs^2:=
    HT.trans ((mul_le_mul_of_nonneg_right hne (mul_nonneg (hW n).le (sq_nonneg _))).trans_eq (one_mul _))
  have Hpow : ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dim n)))
      (by norm_num)
  have Hrate : Cd*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2≤Cd*(W n)^2:=by
    have H1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow hCd.le) (sq_nonneg (M n).xs)
    simp only [mul_one] at H1
    exact H1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (M n).hxs.le (hxs n) 2) hCd.le)
  have HD':=HD.trans (add_le_add Hrate le_rfl)
  refine ⟨hs,hU,?_⟩
  exact susceptibility_pending_envelope_absorption (hW n) hcS hT.le (M n).hxs.le (hxs n)
    hCd.le HB HD' HT'

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_post_Taylor_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePostTaylorCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_pending_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hps := G.pullback
  have Hshell := G.pullback
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_post_Taylor_envelope_along_of_pullback_clocks
    depth Bclock T Cf (Ku+1) cK cKcut hT.le hCf (by linarith) hcK hcKcut
    (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hFirst hFirstLower
    dim hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource
    (Filter.Eventually.of_forall hcompare) Hshell w high outer hw Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_post_longitudinal_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePostLongitudinalCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_post_Taylor_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_selected_bad_history_constant_post_longitudinal_envelope_along_comparable_context (c0:=c0)
    (Ccal:=Ccal) depth (Ku+1) (by linarith) le_rfl hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin hdim M
    G W (fun n=>Kv*W n) hcanonical hWlim
    (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_three_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourceThreeCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_post_longitudinal_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_three_category_envelope_along_of_pullback_clocks
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell (actualSlowWindowExponent m delta/256)
    (div_nonneg (actualSlowWindowExponent_pos hm hdelta hroom).le (by norm_num)) w high outer hw Hmixed Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_b0_category_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourceB0CategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_three_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_b0_category_envelope_along_of_pullback_clocks
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell w high outer hw Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_closed_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_b0_category_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cbond,hCbond,Hbond⟩:=actual_selected_bad_history_susceptibility_coefficient_along_comparable_context (c0:=c0)
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim w hw
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_full_b0_envelope_saving_along_of_pullback_clocks
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hmacro hRhalf hCx
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell w high outer hw Hstrong
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS)+Cbond,by positivity,?_⟩
  filter_upwards [HB,HT,Herr,Hbond] with n hnB hnT hne hnBond
  intro Lnet us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter hnodes] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans Hsmall
  have Hgap : |T*
      (scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us j)
        (relocatedClock (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) 0
          (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us j))))).H 0 0^2-1| ≤
      (Cb+2*(T/cS))*(W n)^2:=by
    apply HB.trans
    have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
    have H':=add_le_add_left H (Cb*(W n)^2)
    convert H' using 1 <;> ring
  have HBond:=hnBond (finiteCutMasses us j) (finiteCutMasses_ordered us hus j)
    (finiteCutMasses_nodes us j hstar) _ hs hU
  refine ⟨hs,hU,?_,?_⟩
  · apply Hgap.trans
    nlinarith [sq_nonneg (W n)]
  · apply HBond.trans
    nlinarith only [Hgap]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (_hmacro : 0 < Rmacro) (_hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (_hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (_Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hfactor : 0 ≤ T/cS:=div_nonneg hT.le hcS.le
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hsaving : 0 ≤ actualSlowWindowExponent m delta/256:=
    (div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)).le
  let rho:=min m (actualMassSavingExponent m delta/256)
  have hrho : 0 ≤ rho:=le_min hm.le (div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num))
  obtain ⟨Cb,hCb,HB⟩:=actual_selected_bad_history_susceptibility_by_other_sources_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hc0 hc01 (by linarith : 0 ≤ Ku+1)
    hmargin hcapmargin hgapmargin hcK hsaving
    (div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)) htau depth
    dim hdim M G W hcanonical hWlim
    w hw high outer (fun n=>Kv*W n) Hcuts Hknown
  obtain ⟨Ce,hCe,HE⟩:=actual_selected_bad_history_constant_source_category_envelope_along_comparable_context (c0:=c0)
    (eta:=m) depth (Ku+1) (by linarith) le_rfl hcKcut hcK hFirst hFirstLower hm (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin hdim
    M G W (fun n=>Kv*W n)
    hcanonical hWlim hcompare (actualSlowWindowExponent m delta/256) hsaving w Hmixed high outer Hcuts
  let C:=Cb+2*(T/cS)*Ce
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,HE] with n hnB hnE
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB us hus hstar hhigh houter,hnE Lnet us hus hret hmesh hstar hhigh houter]
    with j hjB hjE
  dsimp only at hjB hjE ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HE⟩:=hjE
  refine ⟨hs,hU,?_⟩
  let N:=((dim n+1:ℕ):ℝ)
  have hN : 1 ≤ N:=by dsimp only [N];exact_mod_cast (show 1 ≤ dim n+1 by omega)
  have hpow : N^(-rho) ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hrho)
  have hxs2 : (M n).xs^2 ≤ (W n)^2:=by nlinarith [(M n).hxs,hxs n]
  have Hrate : Ce*N^(-rho)*(M n).xs^2 ≤ Ce*(W n)^2:=by
    have H:=(mul_le_mul_of_nonneg_right hpow (sq_nonneg (M n).xs)).trans (by simpa using hxs2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H hCe.le
  have HE' : nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth ≤
      Ce*(W n)^2+nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth:=
    HE.trans (add_le_add Hrate le_rfl)
  have HH:=mul_le_mul_of_nonneg_left HE' hfactor
  dsimp only [C,cS] at HH ⊢
  nlinarith only [HB,HH]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_taylor_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceTaylorPart (M n) as star U|/(cS*W n)) := by
  have hTemp : 0  <  T := G.hT
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cr,hCr,HR⟩:=actual_selected_bad_history_constant_source_remainder_on_given_cuts_along_comparable_context (c0:=c0)
    (by linarith : 0 ≤ Ku+1) hFirst hFirstLower hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim M G
    W (fun n=>Kv*W n) hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  refine ⟨Cb+2*Cr/cS,by positivity,?_⟩
  filter_upwards [HB,HR] with n hnB hnR
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnR Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjR
  dsimp only at hjB hjR ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  refine ⟨hs,hU,?_⟩
  exact susceptibility_bootstrap_remainder_reduction
    ((M n).hxs.trans_le (hxs n)) hcS (M n).hxs.le (hxs n) hCr.le HB hjR

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_pending_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePendingCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨err,herr,HTaylor⟩:=actual_selected_bad_history_constant_joint_Taylor_rate_along_comparable_context (c0:=c0)
    (Ccompare:=Ccal^2) (Ku+1) hT.le (by linarith) (sq_nonneg Ccal)
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hFirst hFirstLower hmargin hcapmargin
    dim hdim M G W hcanonical hWlim w hw
    (Filter.Eventually.of_forall hcompare)
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_taylor_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨Cd,hCd,HD⟩:=actual_selected_bad_history_constant_pending_category_envelope_along_comparable_context (c0:=c0)
    depth (Ku+1) (by linarith) le_rfl hcKcut hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin hdim M G
    W (fun n=>Kv*W n) hcanonical hWlim w high outer Hcuts
  refine ⟨Cb+2*(T/cS)*Cd+2/cS,by positivity,?_⟩
  filter_upwards [HB,HD,HTaylor,Herr,Hcuts] with n hnB hnD hnT hne hnCuts
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnD Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hstar hret hmesh] with j hjB hjD hjT
  dsimp only at hjB hjD hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HD⟩:=hjD
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  obtain ⟨_,HUV,HV,Hlo,_,Houter,_,_,_,_,_,_,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  have Hupper : partitionPoint 0 as U≤ min ((Ku+1)*W n) 1:=by
    refine le_min ?_ (partitionPoint_mem as ho U).2
    exact (partitionPoint_mono as ho HUV.le).trans Houter
  have HT:=hjT U hs hU Hlo Hupper
  have HS : (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k))=
      nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as:=by
    funext k
    exact native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone (partitionPoint_mem as ho k)
  change |nativeActualJointRestoredForwardTaylorError (dim n) _ U _ _ _
    (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k)) _ _ _ _|≤_ at HT
  rw [HS] at HT
  change |nativeActualConstantSourceTaylorPart (M n) as star U|≤err n*(W n*(M n).xs^2) at HT
  have HT' : |nativeActualConstantSourceTaylorPart (M n) as star U|≤W n*(M n).xs^2:=
    HT.trans ((mul_le_mul_of_nonneg_right hne (mul_nonneg (hW n).le (sq_nonneg _))).trans_eq (one_mul _))
  have Hpow : ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dim n)))
      (by norm_num)
  have Hrate : Cd*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2≤Cd*(W n)^2:=by
    have H1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow hCd.le) (sq_nonneg (M n).xs)
    simp only [mul_one] at H1
    exact H1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (M n).hxs.le (hxs n) 2) hCd.le)
  have HD':=HD.trans (add_le_add Hrate le_rfl)
  refine ⟨hs,hU,?_⟩
  exact susceptibility_pending_envelope_absorption (hW n) hcS hT.le (M n).hxs.le (hxs n)
    hCd.le HB HD' HT'

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_post_taylor_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePostTaylorCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hps := G.pullback
  have Hshell := G.pullback
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_pending_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_post_Taylor_envelope_along_of_pullback_clocks
    depth Bclock T Cf (Ku+1) cK cKcut hT.le hCf (by linarith) hcK hcKcut
    (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hFirst hFirstLower
    dim hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource
    (Filter.Eventually.of_forall hcompare) Hshell w high outer hw Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_post_longitudinal_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourcePostLongitudinalCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_post_taylor_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨err,herr,HT⟩:=actual_selected_bad_history_constant_post_longitudinal_envelope_along_comparable_context (c0:=c0)
    (Ccal:=Ccal) depth (Ku+1) (by linarith) le_rfl hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin hdim M
    G W (fun n=>Kv*W n) hcanonical hWlim
    (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_three_categories_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourceThreeCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_post_longitudinal_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_three_category_envelope_along_of_pullback_clocks
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell (actualSlowWindowExponent m delta/256)
    (div_nonneg (actualSlowWindowExponent_pos hm hdelta hroom).le (by norm_num)) w high outer hw Hmixed Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_b0_category_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |T*chi^2-1|≤C*(W n)^2+
            2*(T/cS)*nativeActualConstantSourceB0CategoryEnvelope (M n) hs hU (W n) T cK depth := by
  have hTemp : 0  <  T := G.hT
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_three_categories_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_b0_category_envelope_along_of_pullback_clocks
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell w high outer hw Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_closed_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w)
    (hRhalf : Rmacro ≤ 1/2) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  have hTemp : 0  <  T := G.hT
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cbond,hCbond,Hbond⟩:=actual_selected_bad_history_susceptibility_coefficient_along_comparable_context (c0:=c0)
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim w hw
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_b0_category_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_full_b0_envelope_saving_along_of_pullback_clocks
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hmacro hRhalf hCx
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell w high outer hw Hstrong
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS)+Cbond,by positivity,?_⟩
  filter_upwards [HB,HT,Herr,Hbond] with n hnB hnT hne hnBond
  intro Lnet us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter hnodes] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans Hsmall
  have Hgap : |T*
      (scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us j)
        (relocatedClock (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) 0
          (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us j))))).H 0 0^2-1| ≤
      (Cb+2*(T/cS))*(W n)^2:=by
    apply HB.trans
    have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
    have H':=add_le_add_left H (Cb*(W n)^2)
    convert H' using 1 <;> ring
  have HBond:=hnBond (finiteCutMasses us j) (finiteCutMasses_ordered us hus j)
    (finiteCutMasses_nodes us j hstar) _ hs hU
  refine ⟨hs,hU,?_,?_⟩
  · apply Hgap.trans
    nlinarith [sq_nonneg (W n)]
  · apply HBond.trans
    nlinarith only [Hgap]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_susceptibility_at_sharp_window_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cwindow : ℝ) (hCwindow : 0 < Cwindow) (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨hsaving,hsharp,cK,hcK,_Htotal,Cf,hCf,Hsource,_hw,_HK,Hsquare,Hmixed,Hconstant,
    _Hpair,_Hfrozen,_Hinitial,threshold,hthreshold,tau,htau,Hknown⟩:=
    actual_selected_bad_history_constant_source_known_envelope_at_sharp_window_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      Cwindow hCwindow w hw
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong⟩:=
    exists_actual_strong_sharp_source_cuts_along Rmacro Cx hmacro hCx hcl hcu hAz hTemp hL M W hxs hWlim w hw
  refine ⟨cK,hcK,Cf,hCf,Hsource,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  exact actual_given_sharp_star_strong_cuts_closed_along_comparable_context (c0:=c0)
    Rmacro Cx hmacro hCx
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim hcompare
    hcK hCf hKu hFirst hFirstLower hcKcut htau.le Hsource w hw Hmixed high outer Hstrong depth
    (Hknown depth hd).2 hRhalf

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum

theorem exists_actual_selected_bad_history_sharp_window_sequence_later_half_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ctest c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      ∀ᶠn in atTop,(calibratedBandStart cu Az+2*L)*W n < (w n).star.val := by
  exact exists_actual_comparable_context_sharp_window_sequence_later_half
    hm hdelta hroom hcl hcu hAz hC0 hCt hCtest hL dim hdim M G
    W hcanonical hWlim hcompare

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_later_half_susceptibility_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀ᶠn in atTop,(calibratedBandStart cu Az+2*L)*W n < (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨Cwindow,hCwindow,w,hw,Hlate⟩:=
    exists_actual_selected_bad_history_sharp_window_sequence_later_half_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hL hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G
      W hcanonical hWlim hcompare
  obtain ⟨cK,hcK,Cf,hCf,Hsource,_hw,Hsquare,Hmixed,Hconstant,Hcuts⟩:=
    actual_selected_bad_history_susceptibility_at_sharp_window_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
      Cwindow hCwindow w hw
  exact ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hlate,Hsquare,Hmixed,Hconstant,Hcuts⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_covered_target_susceptibility_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 ≤ Atarget)
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T (Atarget+1) Cwindow (w n)) ∧
      (∀ᶠn in atTop,(calibratedBandStart cu Az+2*(Atarget+1))*W n < (w n).star.val) ∧
      (∀ᶠn in atTop,Atarget*(M n).xs < (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  have hTemp : 0  <  T := G.hT
  have hL : 0 < Atarget+1:=by linarith
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hlate,Hsquare,Hmixed,Hconstant,Hcuts⟩:=
    exists_actual_selected_bad_history_later_half_susceptibility_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have Hcoverage : ∀ᶠn in atTop,Atarget*(M n).xs < (w n).star.val:=by
    have ha:=calibrated_band_start_pos hcu hAz
    filter_upwards [Hlate] with n hn
    have hx : (M n).xs ≤ W n:=by
      rw [hcanonical]
      exact (M n).canonical_direct_test_band_ge_scale
    have hW : 0 ≤ W n:=(M n).hxs.le.trans hx
    have H1:=mul_le_mul_of_nonneg_left hx hAtarget
    have H2:=mul_le_mul_of_nonneg_right
      (show Atarget ≤ calibratedBandStart cu Az+2*(Atarget+1) by linarith) hW
    exact (H1.trans H2).trans_lt hn
  exact ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hlate,Hcoverage,Hsquare,Hmixed,Hconstant,Hcuts⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_G_cut_comparison_vanishing_envelope_along_comparable_context
    (Bclock Temp Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut) (houter : 0 < Couter)
    {m delta cl cu Az C0 Ct D Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U V : ℕ,i<U → U ≤ V → V ≤ as.length →
          partitionPoint 0 as i ≤ Ccut*x n →
          partitionPoint 0 as V ≤ Couter*(M n).canonicalDirectTestBandScale →
          abs (nativeActualTargetLongitudinalResponse (M n) as i U-
            nativeActualTargetLongitudinalResponse (M n) as i V) ≤ eta n*(x n)^3 ∧
          abs (nativeActualTargetConditionalResponse (M n) as i U-
            nativeActualTargetConditionalResponse (M n) as i V) ≤ eta n*(x n)^3 := by
  obtain ⟨Cf,hCf,Hsource⟩ := NativeOverlapMinimum.actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M G
  have Hps := G.pullback
  apply actual_inherited_target_G_cut_comparison_vanishing_envelope_along
    Bclock Temp Cf Ccut Couter hTemp hCf hCcut houter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs dim hdim M Hsource _ x hxs hxlim hsmall hWlim
  exact G.pullback

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization
open scoped Topology NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_initial_four_reduction_along_comparable_context
    (Bclock Temp : ℝ) (hTemp : 0≤Temp)
    {m delta cl cu Az C0 Ct D c0 : ℝ} (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs≤x n) (hxlim : Tendsto x atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1) →∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
        (W : ℝ),W≠0 → 0<nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
      ∀depth : ℕ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        abs (nativeActualTargetLongitudinalResponse (M n) as i U-
          (nativeActualMinimumFourResidualSum (M n) hs hU W depth [st]+
            nativeActualOriginalContinuumCenteredFourGFrontier (M n) as W i star U hi hs hU depth))≤
          ((dim n+1:ℕ):ℝ)^(-m)*(x n)^3 := by
  have Hrate:=hdim.eventually (eventually_actual_inherited_initial_frozen_response_cubic
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    Bclock Temp hTemp hm hC0)
  have Htotal:=NativeOverlapMinimum.actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0)
    dim M G
  have HX:=hxlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [Hrate,Htotal,HX] with n hn ht hx
  intro us hus
  filter_upwards [hn (M n) ht.1 ht.2 ((hxs n).trans hx) us hus] with jGrid hj
  dsimp only at hj ⊢
  intro i star U hi hs hU W hW hK depth
  have H:=actual_target_response_eq_four_iteration (M n) (finiteCutMasses us jGrid) W i star U hi hs hU
    (finiteCutMasses_ordered us hus jGrid) hW hK depth
  dsimp only at H
  rw [H,sub_sub_cancel_left,abs_neg]
  exact hj i star U (hi.trans (hs.le.trans hU)) W (x n) (hxs n)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_closed_target_initial_residual_joint_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
        (actualMassSavingExponent m delta/32) M W w ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
        ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∃thresholdI : ℕ,0 < thresholdI ∧ ∃savingI : ℝ,0 < savingI ∧
        ∀depth : ℕ,thresholdI ≤ depth → ActualTargetInitialResidualApproxAlong depth savingI Cmass M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_closed_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hsaving:0 < actualSlowWindowExponent m delta/256:=
    div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)
  have hT:0 < T:=G.hT
  have hxs n:(M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hpair (Cmass : ℝ) (hCm : 0 ≤ Cmass) (degree : ℕ) (hd : 0 < degree):=
    actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along degree hd
      hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf Cmass hCm
      dim hdim M W hxs hWlim Hsource w (Hsquare (degree-1))
  have Hsharp:=eventually_actual_sharp_star_inherited_endpoint_second_along
    hm hdelta hC0 hCf dim hdim M W hcanonical hWlim w Hsource hw
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0)
    dim M G
  have Happrox (Cmass : ℝ) (hCm : 0 ≤ Cmass):=
    exists_actual_same_star_initial_residual_approx_along hm hcu hAz hC0 hT.le hTemp hsaving Cmass
      dim hdim M W hxs hWlim (Htotal.mono fun _ h=>h.1) (Htotal.mono fun _ h=>h.2)
      w hw (Hpair Cmass hCm)
  exact ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hsharp,Hconstant,
    Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_covered_target_initial_inputs_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 ≤ Atarget)
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T (Atarget+1) Cwindow (w n)) ∧
      (∀ᶠn in atTop,Atarget*(M n).xs < (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
        (actualMassSavingExponent m delta/32) M W w ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
        ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∃thresholdI : ℕ,0 < thresholdI ∧ ∃savingI : ℝ,0 < savingI ∧
        ∀depth : ℕ,thresholdI ≤ depth → ActualTargetInitialResidualApproxAlong depth savingI Cmass M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,_Hlate,Hcoverage,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_covered_target_susceptibility_along_comparable_context (c0:=c0)
      Atarget hAtarget Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hsaving:0 < actualSlowWindowExponent m delta/256:=
    div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)
  have hT:0 < T:=G.hT
  have hxs n:(M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hpair (Cmass : ℝ) (hCm : 0 ≤ Cmass) (degree : ℕ) (hd : 0 < degree):=
    actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along degree hd
      hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf Cmass hCm
      dim hdim M W hxs hWlim Hsource w (Hsquare (degree-1))
  have Hsharp:=eventually_actual_sharp_star_inherited_endpoint_second_along
    hm hdelta hC0 hCf dim hdim M W hcanonical hWlim w Hsource hw
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0)
    dim M G
  have Happrox (Cmass : ℝ) (hCm : 0 ≤ Cmass):=
    exists_actual_same_star_initial_residual_approx_along hm hcu hAz hC0 hT.le hTemp hsaving Cmass
      dim hdim M W hxs hWlim (Htotal.mono fun _ h=>h.1) (Htotal.mono fun _ h=>h.2)
      w hw (Hpair Cmass hCm)
  exact ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hcoverage,Hsquare,Hmixed,Hsharp,Hconstant,
    Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 18000000

theorem actual_selected_bad_history_four_first_high_initial_rate_along_comparable_context
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=(M n).canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (a : ℝ),
          2*c*W ≤ partitionPoint 0 as U →
          partitionPoint 0 as i ≤ Cmass*(M n).xs → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU W depth
          [nativeActualInitialState as i star a (by omega)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U W Q|)).sum ≤
          C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^3 := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_four_first_high_initial_rate_of_pullback_clocks
    (D:=D) depth Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu) cK
    hTemp hCf hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*(M n).canonicalDirectTestBandScale ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,Hps,hcompare,HW,HG] with n hn hs hp hcali hw hg
  exact hn (M n) 
    hp hs hcali (by norm_num at hw ⊢;exact hw) (by norm_num at hg ⊢;exact hg)

theorem actual_selected_bad_history_four_first_high_projected_constant_rate_along_comparable_context
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=(M n).canonicalDirectTestBandScale
        ∀(star U : ℕ) (hs : star<U) (hU : U ≤ as.length),
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU W depth
          [(nativeActualConstantState as 0 star).projection (hs.le.trans hU)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U W Q|)).sum ≤
          C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2 := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_four_first_high_projected_constant_rate_of_pullback_clocks
    (D:=D) depth Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu) cK
    hTemp hCf hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*(M n).canonicalDirectTestBandScale ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,Hps,hcompare,HW,HG] with n hn hs hp hcali hw hg
  exact hn (M n) 
    hp hs hcali (by norm_num at hw ⊢;exact hw) (by norm_num at hg ⊢;exact hg)

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_first_high_on_given_source_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0≤Cmass) (hA : A≤Cmass)
    (hcK : 0<cK) (hFirst : 0<cFirst) (hFirstLower : 2*cu*(Az+1)≤cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃Ci Cc : ℝ,0<Ci ∧ 0<Cc ∧
      ActualSharpSourceFirstHighInitialOnEveryFinalNetAlong depth Cmass Ci M W w high outer ∧
      ActualSharpSourceFirstHighConstantOnEveryFinalNetAlong depth Cc M W w high outer := by
  have hTemp : 0≤Temp := G.hT.le
  have hWlim' : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE : W=(fun n=>(M n).canonicalDirectTestBandScale):=funext hcanonical
    simpa only [HE] using hWlim
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Ci,hCi,HI⟩:=actual_selected_bad_history_four_first_high_initial_rate_along_comparable_context (c0:=c0)
    depth Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hFirst hFirstLower dim hdim M G hWlim' hcompare
  obtain ⟨Cc,hCc,HC⟩:=actual_selected_bad_history_four_first_high_projected_constant_rate_along_comparable_context (c0:=c0)
    depth Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hFirst hFirstLower dim hdim M G hWlim' hcompare
  refine ⟨Ci,Cc,hCi,hCc,?_,?_⟩
  · filter_upwards [HI,Hcuts] with n hn hnCuts
    intro L us hus hret hmesh hstar hhigh houter
    filter_upwards [hn L us hus hret hmesh] with j hj
    dsimp only at hj ⊢
    obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,_,_,_,_,_,HK,_⟩:=
      hnCuts.finite_net_readout us hus hstar hhigh houter j
    intro pre mid tail hcut hindex
    have hs : pre.length+mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
      rw [hindex]
      exact Hs
    have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(pre++(mid++tail)).length:=by
      rw [hcut]
      exact HUV.le.trans HV
    refine ⟨hs,hU,?_⟩
    intro a hmi
    have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
    have Hmass' := Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
    have H:=hj pre.length (pre.length+mid.length) _ (by omega) hs
      (by simpa only [hcut] using hU) a
      (by simpa only [hcanonical n] using Hfirst) hmi
      (by simpa only [hindex,hcanonical n] using Hmass') (by simpa only [hindex,hcanonical n] using HK)
    let G : List PositiveMass→Prop:=fun bs=>
      ∀hU' : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤bs.length,
      ((nativeActualMinimumFourCenteredForest (M n) hs hU' (W n) depth
        [nativeActualInitialState bs pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourFirstHighError (M n)
          (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) (W n) Q|)).sum ≤
        Ci*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^3
    have HG : G (finiteCutMasses us j):=by
      intro hU'
      simpa only [hcanonical n] using H
    have HG' : G (pre++(mid++tail)):=hcut.symm ▸ HG
    exact HG' hU
  · filter_upwards [HC,Hcuts] with n hn hnCuts
    intro L us hus hret hmesh hstar hhigh houter
    filter_upwards [hn L us hus hret hmesh] with j hj
    dsimp only at hj ⊢
    obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,_,_,_,_,_,HK,_⟩:=
      hnCuts.finite_net_readout us hus hstar hhigh houter j
    intro mid tail hcut hindex
    have hs : mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
      rw [hindex]
      exact Hs
    have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(mid++tail).length:=by
      rw [hcut]
      exact HUV.le.trans HV
    refine ⟨hs,hU,?_⟩
    have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
    have Hmass' := Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
    have H:=hj mid.length _ hs (by simpa only [hcut] using hU)
      (by simpa only [hcanonical n] using Hfirst)
      (by simpa only [hindex,hcanonical n] using Hmass') (by simpa only [hindex,hcanonical n] using HK)
    let G : List PositiveMass→Prop:=fun bs=>
      ∀hU' : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤bs.length,
      ((nativeActualMinimumFourCenteredForest (M n) hs hU' (W n) depth
        [(nativeActualConstantState bs 0 mid.length).projection (hs.le.trans hU')]).map
        (fun Q=>|nativeActualOriginalFourFirstHighError (M n)
          (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) (W n) Q|)).sum ≤
        Cc*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2
    have HG : G (finiteCutMasses us j):=by
      intro hU'
      simpa only [hcanonical n] using H
    have HG' : G (mid++tail):=hcut.symm ▸ HG
    exact HG' hU

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_history_initial_frozen_child_envelope_of_pair_budgets_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp gamma c0 Cmass c cK A : ℝ}
    (depth : ℕ) (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp)
    (hgamma : 0 < gamma) (hcK : 0 < cK) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A)
    (Hpair : ∀d : ℕ,d<depth → ∃B : ℝ,1 ≤ B ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong (d+2) B gamma Cmass M W w) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFrozenChildEnvelopeOnGivenCutsAlong depth Cmass err M W w high outer := by
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  have HK:=Hcuts.mono (fun _ hn=>hn.clock_star)
  have Hlevels (d : ℕ) (hd : d<depth) : ActualOriginalFourFrozenChildLevelSavingAlong d Cmass M W w:=by
    obtain ⟨B,hB,HP⟩:=Hpair d hd
    exact actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
      hm hC0 hTemp hgamma hcK d hB Cmass dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK HP
  let err n:=(depth:ℝ)*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)
  have Hlim : Tendsto err atTop (𝓝 0):=by
    have H:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [err,Function.comp_def,mul_zero,neg_div] using H.const_mul (depth:ℝ)
  exact ⟨err,(fun n=>by dsimp only [err];positivity),Hlim,
    actual_initial_frozen_child_envelope_of_levels_along depth M W radius w high outer Hcuts Hlevels⟩

theorem actual_selected_bad_history_initial_frozen_child_envelope_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp gamma c0 Cmass c cK A : ℝ}
    (depth : ℕ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgamma : 0 < gamma) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A)
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p gamma M W w) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFrozenChildEnvelopeOnGivenCutsAlong depth Cmass err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim
    M G
  have hxs n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  apply actual_history_initial_frozen_child_envelope_of_pair_budgets_along_comparable_context (c0:=c0) depth hm hC0 hTemp
    hgamma hcK hdim M G W radius hxs w high outer Hcuts
  intro d _hd
  exact actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along (d+2) (by omega)
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf Cmass hCm
    dim hdim M W hxs hWlim Hsource w (Hsquare (d+2-1))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_saved_nonLOW_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualHistoryInitialSavedNonLowOnGivenCutsAlong depth A err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim
    M G
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨CF,_,hCF,_,HF,_⟩:=actual_selected_bad_history_first_high_on_given_source_cuts_along_comparable_context (c0:=c0)
    depth A (zero_le_one.trans hA) le_rfl hcK hc hcouter
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin hdim
    M G W radius hcanonical hWlim
    (Eventually.of_forall hcompare) w high outer Hcuts
  obtain ⟨CG,hCG,HG0⟩:=eventually_inherited_same_star_four_Ga_current_initial_along
    (eta:=m) hdim depth A cK hA hcK hm hm hdelta hroom (by linarith)
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare Hsource saving hsaving w Hmixed
  have HG:=HG0.on_sharp_source_cuts hxs le_rfl Hcuts
  obtain ⟨eR,heR,eRlim,HR⟩:=actual_inherited_initial_restored_Ga_on_given_cuts_along_of_pullback_clocks
    depth hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W radius hcanonical hWlim Hsource (Eventually.of_forall hcompare) Hshell w high outer Hcuts
  obtain ⟨eD,heD,eDlim,HD⟩:=actual_inherited_initial_deleted_site_on_given_cuts_along
    depth hA hcK hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf
    hdim M W radius hcanonical hWlim Hsource w high outer Hcuts
  let eF n:=CF*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  let eG n:=CG*(dim n:ℝ)^(-m)
  let err n:=eF n+eG n+eR n+eD n
  have eFlim : Tendsto eF atTop (𝓝 0):=by
    have H:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
      (by norm_num : (0:ℝ)<256))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [eF,Function.comp_def,mul_zero] using H.const_mul CF
  have eGlim : Tendsto eG atTop (𝓝 0):=by
    simpa only [eG,Function.comp_def,mul_zero] using
      ((tendsto_rpow_neg_atTop hm).comp (tendsto_natCast_atTop_atTop.comp hdim)).const_mul CG
  have herr n : 0 ≤ err n:=by
    dsimp only [err,eF,eG]
    exact add_nonneg (add_nonneg (add_nonneg (by positivity) (by positivity)) (heR n)) (heD n)
  have errlim : Tendsto err atTop (𝓝 0):=by
    simpa only [err,zero_add] using ((eFlim.add eGlim).add eRlim).add eDlim
  refine ⟨err,herr,errlim,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HF,HG,HR,HD,Hcuts,Hsource,HW] with n hnF hnG hnR hnD hcuts hsClocks hW1
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hnF L us hus hret hmesh hstar hhigh houter,
    hnG L us hus hret hmesh hstar hhigh houter,
    hnR L us hus hret hmesh hstar hhigh houter,
    hnD L us hus hret hmesh hstar hhigh houter] with jGrid hjF hjG hjR hjD
  dsimp only at hjF hjG hjR hjD ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  intro pre mid tail hcut hindex hmid hmi
  obtain ⟨HI,HU,HF⟩:=hjF pre mid tail hcut hindex
  obtain ⟨_,_,HG⟩:=hjG pre mid tail hcut hindex hmid
  obtain ⟨_,_,HR⟩:=hjR pre mid tail hcut hindex hmid hmi
  obtain ⟨_,_,HD⟩:=hjD pre mid tail hcut hindex hmid hmi
  refine ⟨HI,HU,?_⟩
  intro seedMass
  let old:=pre++(mid++tail)
  let i:=pre.length
  let star:=pre.length+mid.length
  have hi : i ≤ star:=by dsimp only [i,star];omega
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old i star seedMass (hi.trans (HI.le.trans HU))
  let rows:=nativeActualMinimumFourCenteredForest (M n) HI HU (W n) depth [st]
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed old HU seedMass .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
  have Hvalid : ∀Q∈rows,NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term:=by
    apply nativeActualFourCenteredForest_valid
    intro Q hQ
    have HQ : Q=st:=List.mem_singleton.mp hQ
    subst Q
    exact hP
  have ho : MassOrdered 0 old:=by dsimp only [old];rw [hcut];exact finiteCutMasses_ordered us hus jGrid
  have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old star:=by
    dsimp only [old,star];rw [hcut,hindex];exact HstarK
  have HF' : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U (W n) Q|)).sum ≤
      eF n*(M n).xs^3:=by exact HF seedMass hmi
  have HG' : (rows.map (fun Q=>|nativeActualOriginalFourGaCurrentError (M n) U (W n) Q|)).sum ≤
      eG n*(M n).xs^3:=by
    apply (HG seedMass (M n).xs le_rfl (hxs n) hmi).trans_eq
    dsimp only [eG]
    ring
  have H:=actual_initial_saved_nonLOW_envelope_le (M n) hCf hsClocks ((hxs n).trans hW1)
    ho hi HI HU hW hcK HK rows Hvalid HG' (HR seedMass) HF' (HD seedMass)
  apply H.trans_eq
  dsimp only [err]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_closed_initial_feedback_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
        (actualMassSavingExponent m delta/32) M W w ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
        ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∃thresholdI : ℕ,0 < thresholdI ∧ ∃savingI : ℝ,0 < savingI ∧
        ∀depth : ℕ,thresholdI ≤ depth → ActualTargetInitialResidualApproxAlong depth savingI Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀depth : ℕ,
        ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀k0 depth r : ℕ,
        ActualOriginalFourInitialPairForestSavingAlong k0 depth r saving
          (actualMassSavingExponent m delta/32) Cmass M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧(∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |T*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀feedbackDepth : ℕ,∃err : ℕ→ℝ,
          (∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
          ActualInitialPairFeedbackResidualOnStrongCutsAlong feedbackDepth T cKcut Cmass err M W w high outer) := by
  have hTemp : 0  <  T := G.hT
  obtain ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hsharp,Hconstant,
    Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_closed_target_initial_residual_joint_along_comparable_context (c0:=c0)
      Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hT : 0 < T:=G.hT
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0)
    dim M G
  have Hclock:=Hstrong.mono (fun _ hn=>hn.clock_star)
  have hsharp : 0 < actualMassSavingExponent m delta/32:=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have Hnum (Cmass : ℝ) (hCm : 0 ≤ Cmass):=
    actual_same_star_initial_four_numeric_inputs_along hm hC0 hT.le hsaving hsharp hcKcut
      Cmass dim hdim M W hxs (Htotal.mono fun _ hn=>hn.1) (Htotal.mono fun _ hn=>hn.2)
      w Hclock (Hpair Cmass hCm) Hsharp
  refine ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hsharp,Hconstant,
    Hpair,Happrox,(fun Cmass hCm=>(Hnum Cmass hCm).2.1),
    (fun Cmass hCm=>(Hnum Cmass hCm).2.2),Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,
    hcKcut,high,outer,Hvalues,Hstrong,threshold,hthreshold,?_⟩
  intro depth hdepth
  obtain ⟨C,hC,HC⟩:=Hbootstrap depth hdepth
  refine ⟨C,hC,HC,?_⟩
  have HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong C M W w high outer:=by
    filter_upwards [HC] with n hn
    intro Lnet us hus hret hmesh hstar hhigh houter hnodes
    filter_upwards [hn Lnet us hus hret hmesh hstar hhigh houter hnodes] with j hj
    obtain ⟨_,_,_,HJ⟩:=hj
    exact HJ
  intro Cmass hCm feedbackDepth
  exact actual_calibrated_initial_pair_feedback_residual_along feedbackDepth hsaving.le hsharp hcKcut hC.le
    hdim M W (fun n=>Kv*W n) hxs w high outer
    (Hstrong.mono fun _ hn=>hn.toActualSharpSourceCutGeometry) HJ
    (fun d=>(Hnum Cmass hCm).2.2 0 d 2)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_residual_modulo_thermal_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A Tstar Lwin Cwindow Cj : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 < saving) (hCj : 0 ≤ Cj)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w)
    (HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialResidualModuloThermalOnStrongCutsAlong depth A err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim
    M G
  have Hps := G.pullback
  have Hshell := G.pullback
  have hxs n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0) dim M G
  have HP (degree : ℕ) (hd : 0 < degree):=
    actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along degree hd
      hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf A (zero_le_one.trans hA)
      dim hdim M W hxs hWlim Hsource w (Hsquare (degree-1))
  have Hsharp:=eventually_actual_sharp_star_inherited_endpoint_second_along
    hm hdelta hC0 hCf dim hdim M W hcanonical hWlim w Hsource hw
  have hsharp : 0 < actualMassSavingExponent m delta/32:=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have Hnum:=actual_same_star_initial_four_numeric_inputs_along hm hC0 hTemp hsaving hsharp hcK
    A dim hdim M W hxs (Htotal.mono fun _ hn=>hn.1) (Htotal.mono fun _ hn=>hn.2)
    w (Hcuts.mono fun _ hn=>hn.clock_star) HP Hsharp
  obtain ⟨eP,heP,hPlim,Hpair⟩:=actual_calibrated_initial_pair_feedback_residual_along
    (Temp:=Temp) depth hsaving.le hsharp hcK hCj hdim M W radius hxs w high outer Hcuts HJ
    (fun d=>Hnum.2.2 0 d 2)
  obtain ⟨eF,heF,hFlim,Hfrozen⟩:=actual_history_initial_frozen_child_envelope_of_pair_budgets_along_comparable_context (c0:=c0)
    depth hm hC0 hTemp hsaving hcK hdim M G
    W radius hxs w high outer Hcuts (fun d _=>HP (d+2) (by omega))
  have HN d:=actual_selected_bad_history_initial_saved_nonLOW_on_given_cuts_along_comparable_context (c0:=c0)
    d hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim M G W radius hcanonical hWlim hcompare
    saving hsaving.le w high outer Hmixed Hcuts
  choose eN heN hNlim HN using HN
  have HG d:=actual_inherited_initial_three_Gamma_on_given_cuts_along_of_pullback_clocks
    d hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal hdim
    M W radius hcanonical hWlim Hsource (fun n=>(M n).xs) (Eventually.of_forall fun _=>le_rfl)
    (Eventually.of_forall hxs) (Eventually.of_forall hcompare) Hshell saving hsaving.le w high outer hw Hmixed Hcuts
  choose eG heG hGlim HG using HG
  have HL d:=actual_inherited_initial_longitudinal_on_given_cuts_along_of_pullback_clocks
    d (zero_le_one.trans hA) hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hdim
    M W radius hcanonical hWlim Hsource (Eventually.of_forall hcompare) Hshell w high outer Hcuts
  choose eL heL hLlim HL using HL
  let ec d n:=eN d n+eG d n+eL d n
  let err n:=eP n+eF n+((List.range depth).map (fun d=>ec d n)).sum
  have Hclim d : Tendsto (ec d) atTop (𝓝 0):=by
    simpa only [ec,zero_add] using ((hNlim d).add (hGlim d)).add (hLlim d)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>ec d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using (Hclim d).add ih
  refine ⟨err,?_,?_,?_⟩
  · intro n
    dsimp only [err,ec]
    exact add_nonneg (add_nonneg (heP n) (heF n)) (List.sum_nonneg (by
      intro a ha;obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
      exact add_nonneg (add_nonneg (heN d n) (heG d n)) (heL d n)))
  · simpa only [err,zero_add] using (hPlim.add hFlim).add (Hlim (List.range depth))
  · have HNs:=Filter.eventually_all.mpr (fun d : Fin depth=>HN d.val)
    have HGs:=Filter.eventually_all.mpr (fun d : Fin depth=>HG d.val)
    have HLs:=Filter.eventually_all.mpr (fun d : Fin depth=>HL d.val)
    filter_upwards [Hpair,Hfrozen,HNs,HGs,HLs,Hcuts,Htotal] with n hp hf hn hg hl hcuts htotal
    intro L us hus hret hmesh hstar hhigh houter hnodes
    have HNg:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter)
    have HGg:=Filter.eventually_all.mpr (fun d : Fin depth=>hg d L us hus hret hmesh hstar hhigh houter)
    have HLg:=Filter.eventually_all.mpr (fun d : Fin depth=>hl d L us hus hret hmesh hstar hhigh houter)
    filter_upwards [hp L us hus hret hmesh hstar hhigh houter hnodes,
      hf L us hus hret hmesh hstar hhigh houter,HNg,HGg,HLg] with jGrid hjP hjF hjN hjG hjL
    dsimp only at hjP hjF hjN hjG hjL ⊢
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    obtain ⟨hs,HUV,HV,_,_,_,_,_,_,_,_,HstarK,_⟩:=hcuts.finite_net_readout us hus hstar hhigh houter jGrid
    have hU:=HUV.le.trans HV
    obtain ⟨_,_,hjP⟩:=hjP
    obtain ⟨_,_,hjF⟩:=hjF
    intro pre mid tail hparts hindex hmid hmi
    let old:=pre++(mid++tail)
    let s:=pre.length+mid.length
    have hi : pre.length ≤ s:=by dsimp only [s];omega
    have HI : s<U:=by dsimp only [s];rw [hindex];exact hs
    have HU : U ≤ old.length:=by dsimp only [old];rw [hparts];exact hU
    have hi0 : pre.length ≤ star:=by dsimp only [star,as];rw [←hindex];omega
    let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old pre.length s 0 (hi.trans (HI.le.trans HU))
    refine ⟨HI,HU,?_⟩
    have HPa : nativeActualInitialPairFeedbackEnvelope (M n) hs hU (W n) Temp cK depth
        [nativeActualInitialState as pre.length star 0 (hi0.trans (hs.le.trans hU))] ≤eP n*(M n).xs^3:=by
      have H:=hjP pre.length hi0 (M n).xs le_rfl (hxs n) hmi
      apply H.trans_eq
      ring
    have HPb:=actual_initial_seed_function_reindex as old hparts star s hindex hi0 hs hU hi HI HU
      (fun _ _ hs hU rows=>nativeActualInitialPairFeedbackEnvelope (M n) hs hU (W n) Temp cK depth rows) _ HPa
    have HFa : nativeActualFourFrozenChildResidualEnvelope (M n) hs hU (W n) depth
        [nativeActualInitialState as pre.length star 0 (hi0.trans (hs.le.trans hU))] ≤eF n*(M n).xs^3:=by
      have H:=hjF pre.length hi0 (M n).xs le_rfl (hxs n) hmi
      apply H.trans_eq
      ring
    have HFb:=actual_initial_seed_function_reindex as old hparts star s hindex hi0 hs hU hi HI HU
      (fun _ _ hs hU rows=>nativeActualFourFrozenChildResidualEnvelope (M n) hs hU (W n) depth rows) _ HFa
    have Hrow d (hd : d∈List.range depth) :
        nativeActualInitialSavedNonLowEnvelope (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d [st])+
        nativeActualThreeGammaCategoryEnvelope (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d [st])+
        nativeActualInitialLongitudinalEnvelope (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d [st]) ≤ ec d n*(M n).xs^3:=by
      obtain ⟨_,_,HN0⟩:=hjN ⟨d,List.mem_range.mp hd⟩ pre mid tail hparts hindex hmid hmi
      obtain ⟨_,_,HG0⟩:=hjG ⟨d,List.mem_range.mp hd⟩ pre mid tail hparts hindex hmid hmi
      obtain ⟨_,_,HL0⟩:=hjL ⟨d,List.mem_range.mp hd⟩
      have HLa:=HL0 pre.length hi0 (M n).xs le_rfl (hxs n) hmi
      have HLb:=actual_initial_seed_function_reindex as old hparts star s hindex hi0 hs hU hi HI HU
        (fun _ _ hs hU rows=>nativeActualInitialLongitudinalEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d rows)) _ HLa
      have HB:=add_le_add (add_le_add (HN0 0) (HG0 0)) HLb
      apply HB.trans_eq
      dsimp only [ec]
      ring
    have HS:=List.sum_le_sum Hrow
    rw [List.sum_map_add,List.sum_map_add,List.sum_map_mul_right] at HS
    have hvalid : ∀Q∈[st],NativeActualResourceGenerated pre.length s U [.initial] Q.generation Q.tree Q.term:=by
      intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ
      exact .physical (.seed old HU 0 .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
    have HO : MassOrdered 0 old:=by rw [show old=as from hparts];exact finiteCutMasses_ordered us hus jGrid
    have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old s:=by
      dsimp only [old,s];rw [hparts,hindex];exact HstarK
    have Hres:=actual_minimum_four_residual_abs_le_initial_normalized_envelope (M n) htotal.1
      ((M n).hxs.trans_le (hxs n)) hcK HO hi HI HU HK [st] hvalid depth
    rw [actual_initial_normalized_residual_envelope_eq] at Hres
    have Hsaved:=add_le_add (add_le_add HPb HFb) HS
    apply Hres.trans
    dsimp only [err]
    nlinarith only [Hsaved]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem actual_second_low_actual_history_full_weighted_forest_B0_modulus_along_comparable_context
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass Ccut Couter Ccal Rmacro F Cx cK : ℝ) (hcK : 0<cK)
    (hCx : 0 < Cx) (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter) (hCcal : 1 ≤ Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0 ≤ Cf ∧ 0 < Ci ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∃eps : ℕ→ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFullWeightedForestB0ModulusOnEveryFinalNetAlong seedBound k₀ r₀ depth Cmass Ccut Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) cK Ci eps dim M W w := by
  obtain ⟨Cf,Ci,hCf,hCi,HS,eps,heps,HL,H⟩:=actual_second_low_actual_history_full_half_retarget_B0_modulus_along_comparable_context (c0:=c0)
    (seedBound+k₀+depth) (r₀+6*depth) Cmass Ccut Couter Ccal Rmacro F Cx hCx hTemp hCm hCcut hCouter hCcal
    heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hc0 hmargin hcapmargin
    dim hdim M G W hcanonical hWlim w Hcompare hw
  have HX : ∀ᶠn in atTop,(M n).xs ≤ 1:=by
    filter_upwards [hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn
    rw [hcanonical n] at hn
    exact (M n).canonical_direct_test_band_ge_scale.trans hn
  obtain ⟨CiForest,hCiForest,epsForest,hepsForest,HLForest,HForest⟩:=
    actual_second_low_full_weighted_forest_from_actual_half_rows_along seedBound k₀ r₀ depth
      Cmass Ccut Couter Rmacro Cx cK Ci eps hTemp hCf hcK hCi heps HL dim M W w HS HX H
  exact ⟨Cf,CiForest,hCf,hCiForest,HS,epsForest,hepsForest,HLForest,HForest⟩

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_full_b0_on_strong_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal Tstar Lwin Cwindow c0 c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFullB0OnStrongGivenCutsAlong depth A Ci err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  let F:=max (1+2*cu) (1+1/Rmacro)
  obtain ⟨Cf,Ci,hCf,hCi,Hsource,eps,heps,hepslim,HB⟩:=
    actual_second_low_actual_history_full_weighted_forest_B0_modulus_along_comparable_context (c0:=c0)
      (eta:=m) 1 0 2 depth A (A+1) A Ccal Rmacro F Cx cK hcK hCx hTemp hA0.le
      (by positivity) hA0.le hCcal hm hm hdelta hroom (by linarith) hcl hcu hAz hC0 hCt
      hmacro hRhalf (le_max_left _ _) (le_max_right _ _) hc0 hmargin hcapmargin
      dim hdim M G W hcanonical hWlim w hcompare hw
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cout:=Ci*A*Cerr/Cd+1
  let err n:=eps n/Cd
  have hCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCout : 0 < Cout:=by dsimp only [Cout];positivity
  have herr n : 0 ≤ err n:=div_nonneg (heps n) hCd.le
  have errlim : Tendsto err atTop (𝓝 0):=by
    simpa only [err,zero_div] using hepslim.div_const Cd
  refine ⟨Cout,hCout,err,herr,errlim,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HB,Hcuts,Hsource,HW] with n hn hcuts hsClocks hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx0 : 0 < (M n).xs:=(M n).hxs
  have herrn : 0 ≤ err n:=herr n
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hmesh:=uniformMasses_mesh_tendsto.eventually (eventually_le_nhds (M n).hxs)
  filter_upwards [hn L us hus hstar hret hmesh,Hmesh] with jGrid hj hmeshFine
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,_,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  obtain ⟨_,_,_,_,Hhighmass,_,Hfour,HstarR,Hz,HCx,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ A*W n:=(partitionPoint_mono as ho HUV.le).trans Houter
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  refine ⟨HI,HU,?_⟩
  intro seedMass
  let old:=pre++(mid++tail)
  let i:=pre.length
  let star:=pre.length+mid.length
  have hi : i ≤ star:=by dsimp only [i,star];omega
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old i star seedMass (hi.trans (HI.le.trans HU))
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed old HU seedMass .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
  have Hlow : partitionPoint 0 as (pre.length+1) ≤ (A+1)*(M n).xs:=
    actual_initial_successor_low_cut_mass_le hus hmeshFine hmi
  have Hri:=hcuts.finite_net_initial_radius_gap us hus hstar hhigh jGrid pre.length
    (by rw [←hindex];omega)
  have Hraw:=hj pre mid tail hcut.symm hindex (pre.length+1) U HU [.initial] st hP (by simp) rfl
    (nativeActualInitialState_leaves_le old i star seedMass (hi.trans (HI.le.trans HU)))
    hmid (by omega) (by omega) (by omega) HI Hlow Hupper
    (M n).xs (high n).val (high n).property le_rfl hxW hmi
    (by simpa only [hindex] using Hmass) Hfour Hz Hri (by simpa only [hindex] using HstarR)
    (by simpa only [Hhighmass] using HCx) Hhighmass hnodes (by simpa only [hindex] using HstarK)
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one] at Hraw
  have ho' : MassOrdered 0 old:=by dsimp only [old];rw [hcut];exact ho
  have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old star:=by
    dsimp only [old,star];rw [hcut,hindex];exact HstarK
  obtain ⟨hden,_,Hden⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsClocks (hxW.trans hW1) hW hcK ho' HI HU HK
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
  have hDi : 0 ≤ Di:=by dsimp only [Di,nativeOriginalCutLowErrorRadius];positivity
  change 0 < chi*K star at hden
  change Cd*W n ≤ chi*K star at Hden
  change |nativeActualFourOtherCategorySum (M n) U (W n)
    (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) depth [st]) .secondLow|/(chi*K star) ≤
      Cout*(M n).xs^2*Di+err n*(M n).xs^3
  apply (div_le_iff₀ hden).2
  apply Hraw.trans
  have Hmass:=mul_le_mul_of_nonneg_left Hupper
    (show 0 ≤ Ci*Cerr*(M n).xs^2*Di by positivity)
  have Hcoef : Ci*A*Cerr/Cd ≤ Cout:=by dsimp only [Cout];linarith
  have HC:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right Hcoef (sq_nonneg (M n).xs)) hDi
  have HC':=mul_le_mul_of_nonneg_right (add_le_add HC (le_refl (err n*(M n).xs^3)))
    (show 0 ≤ Cd*W n by positivity)
  have HD:=mul_le_mul_of_nonneg_left Hden
    (show 0 ≤ Cout*(M n).xs^2*Di+err n*(M n).xs^3 by positivity)
  apply le_trans ?_ HD
  apply le_trans ?_ HC'
  calc
    _=(Ci*Cerr*(M n).xs^2*Di)*partitionPoint 0 as U+eps n*W n*(M n).xs^3:=by
      dsimp only [Cerr,Di,as]
      ring
    _ ≤ (Ci*Cerr*(M n).xs^2*Di)*(A*W n)+eps n*W n*(M n).xs^3:=
      add_le_add Hmass le_rfl
    _ = _:=by dsimp only [err];field_simp [hCd.ne']

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_full_b0_residual_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal Tstar Lwin Cwindow c0 c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 ≤ Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialFullB0ResidualOnStrongGivenCutsAlong depth A Ci err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  have Hlevels d:=actual_selected_bad_history_initial_full_b0_on_strong_given_cuts_along_comparable_context (c0:=c0)
    d hA hcK hmacro hRhalf hCx hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim M G W radius hcanonical hWlim hcompare
    w high outer hw Hcuts
  choose C hC e he0 helim HE using Hlevels
  let Cout:=((List.range depth).map C).sum
  let err n:=((List.range depth).map (fun d=>e d n)).sum
  have hCout : 0 ≤ Cout:=List.sum_nonneg (by
    intro a ha;obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha;exact (hC d).le)
  have herr n : 0 ≤ err n:=List.sum_nonneg (by
    intro a ha;obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha;exact he0 d n)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>e d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using (helim d).add ih
  refine ⟨Cout,hCout,err,herr,Hlim (List.range depth),?_⟩
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>HE d.val)
  filter_upwards [HN,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter hnodes)
  filter_upwards [Hgrid] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨hs,HUV,HV,_,_,_,_,_,_,_,_,_,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact HUV.le.trans HV
  refine ⟨HI,HU,?_⟩
  intro seedMass
  let old:=pre++(mid++tail)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
  have Hrow d (hd : d∈List.range depth) :
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d
          [nativeActualInitialState old pre.length (pre.length+mid.length) seedMass (by dsimp only [old];omega)])
        .secondLow|/(chi*K (pre.length+mid.length)) ≤ C d*(M n).xs^2*Di+e d n*(M n).xs^3:=by
    obtain ⟨_,_,H⟩:=hj ⟨d,List.mem_range.mp hd⟩ pre mid tail hcut hindex hmid hmi
    exact H seedMass
  have Hsum:=List.sum_le_sum Hrow
  simpa only [nativeActualInitialFullB0ResidualEnvelope,Cout,err,
    List.sum_map_add,List.sum_map_mul_right] using Hsum

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_residual_four_thermal_modulus_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A Tstar Lwin Cwindow Cj Rmacro Cx : ℝ}
    (depth : ℕ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 < saving) (hCj : 0 ≤ Cj)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w)
    (HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 ≤ Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialResidualFourThermalModulusOnStrongCutsAlong depth A Ci err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨eS,heS,hSlim,HS⟩:=actual_selected_bad_history_initial_residual_modulo_thermal_along_comparable_context (c0:=c0)
    depth hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim M G W radius hcanonical hWlim hcompare
    saving hsaving hCj w high outer hw Hsquare HJ Hmixed
    (Hcuts.mono fun _ hn=>hn.toActualSharpSourceCutGeometry)
  obtain ⟨Ci,hCi,eB,heB,hBlim,HB⟩:=actual_selected_bad_history_initial_full_b0_residual_on_given_cuts_along_comparable_context (c0:=c0)
    depth hA hcK hmacro hRhalf hCx hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim M G W radius hcanonical hWlim
    (Eventually.of_forall hcompare) w high outer hw Hcuts
  refine ⟨Ci,hCi,(fun n=>eS n+eB n),(fun n=>add_nonneg (heS n) (heB n)),
    by simpa only [zero_add] using hSlim.add hBlim,?_⟩
  filter_upwards [HS,HB] with n hnS hnB
  intro L us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hnS L us hus hret hmesh hstar hhigh houter hnodes,
    hnB L us hus hret hmesh hstar hhigh houter hnodes] with jGrid hjS hjB
  dsimp only at hjS hjB ⊢
  intro pre mid tail hparts hindex hmid hmi
  obtain ⟨hs,hU,HS0⟩:=hjS pre mid tail hparts hindex hmid hmi
  obtain ⟨_,_,HB0⟩:=hjB pre mid tail hparts hindex hmid hmi
  refine ⟨hs,hU,?_⟩
  rw [actual_initial_thermal_residual_eq_full_B0_add_rest] at HS0
  have H:=HB0 0
  nlinarith only [HS0,H]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_initial_joint_HIGH_categories_rate_along_comparable_context
    (depth : ℕ) (Bclock Temp Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) :
    ∃Cf : ℝ,0 ≤ Cf ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∀kind : NativeJointHighRestorationKind,∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        partitionPoint 0 as i ≤ Cmass*x n →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star seedMass (hi.trans (hs.le.trans hU))
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]) kind.category|/
          (chi*K star) ≤ err n*(x n*(M n).xs^2) := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Hshell := G.pullback
  refine ⟨Cf,hCf,Hsource,?_⟩
  intro kind
  obtain ⟨raw,Hraw,H⟩:=actual_inherited_initial_joint_HIGH_restoration_category_rate_along_of_pullback_clocks
    kind depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource x hxsx hxW hsmall Hshell w
  refine ⟨fun n=>|raw n|,fun n=>abs_nonneg _,?_,?_⟩
  · simpa only [abs_zero] using Hraw.abs
  · filter_upwards [H,hxsx] with n hn hnx
    intro L us hus hret hmesh hstar
    filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
    dsimp only at hj ⊢
    intro i U hi hs hU hcutlo hcut hmi hmassstar hstarK seedMass
    apply (hj i U hi hs hU hcutlo hcut hmi hmassstar hstarK seedMass).trans
    exact mul_le_mul_of_nonneg_right (le_abs_self (raw n))
      (mul_nonneg ((M n).hxs.le.trans hnx) (sq_nonneg _))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 50000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_residual_two_thermal_modulus_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A Tstar Lwin Cwindow Cj Rmacro Cx : ℝ}
    (depth : ℕ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 < saving) (hCj : 0 ≤ Cj)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w)
    (HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 ≤ Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialResidualTwoThermalModulusOnStrongCutsAlong depth A Ci err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  classical
  obtain ⟨Ci,hCi,eFour,heFour,hFourLim,HFour⟩:=actual_selected_bad_history_initial_residual_four_thermal_modulus_along_comparable_context (c0:=c0)
    depth hmacro hRhalf hCx hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0
    hmargin hcapmargin hdim M G W radius hcanonical hWlim
    hcompare saving hsaving hCj w high outer hw Hsquare HJ Hmixed Hcuts
  have hA0:0 ≤ A:=zero_le_one.trans hA
  have hxW:∀ᶠn in atTop,(M n).xs ≤ W n:=Eventually.of_forall (fun n=>by
    rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale)
  have Hlevels d:=actual_selected_bad_history_initial_joint_HIGH_categories_rate_along_comparable_context (c0:=c0)
    (Cs:=Ccal^2) d Bclock Temp A A cK hTemp hA0 hA0 hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    (sq_nonneg Ccal) hc hcouter hc0 hmargin hcapmargin dim hdim M
    W hcanonical hWlim G (fun n=>(M n).xs)
    (Eventually.of_forall (fun _=>le_rfl)) hxW (Eventually.of_forall hcompare) w
  choose Cf hCf Hsource Hkind using Hlevels
  choose eH heH hHlim HH using (fun d=>Hkind d .lowTwoHigh)
  choose eG heG hGlim HG using (fun d=>Hkind d .fourGLow)
  let eJoint n:=((List.range depth).map (fun d=>eH d n+eG d n)).sum
  have heJoint n:0 ≤ eJoint n:=List.sum_nonneg (by
    intro a ha
    obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
    exact add_nonneg (heH d n) (heG d n))
  have Hlim (ls : List ℕ):Tendsto (fun n=>(ls.map (fun d=>eH d n+eG d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using ((hHlim d).add (hGlim d)).add ih
  refine ⟨Ci,hCi,(fun n=>eFour n+eJoint n),(fun n=>add_nonneg (heFour n) (heJoint n)),
    by simpa only [zero_add] using hFourLim.add (Hlim (List.range depth)),?_⟩
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>(HH d.val).and (HG d.val))
  filter_upwards [HFour,Hcuts,HN] with n hnFour hnCuts hn
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>
    (hn d).1 L us hus hret hmesh hstar |>.and ((hn d).2 L us hus hret hmesh hstar))
  filter_upwards [hnFour L us hus hret hmesh hstar hhigh houter hnodes,Hgrid] with jGrid hjFour hj
  dsimp only at hjFour hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨_,HUV,HV,HcutLo,HstarMass,HouterMass,_,_,_,_,_,HstarK,_⟩:=
    hnCuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  have HcutUp:partitionPoint 0 as U ≤ A*W n:=
    (partitionPoint_mono as ho HUV.le).trans HouterMass
  intro pre mid tail hparts hindex hmid hmi
  obtain ⟨hs,hU,HF⟩:=hjFour pre mid tail hparts hindex hmid hmi
  refine ⟨hs,hU,?_⟩
  have hjH d:=(hj d).1
  have hjG d:=(hj d).2
  change 2*c*W n ≤ partitionPoint 0 (finiteCutMasses us jGrid) U at HcutLo
  change partitionPoint 0 (finiteCutMasses us jGrid) U ≤ A*W n at HcutUp
  rw [←hparts] at hjH hjG hindex HcutLo HcutUp HstarMass HstarK hmi
  rw [←hindex] at HstarMass HstarK
  let old:=pre++(mid++tail)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old pre.length (pre.length+mid.length) 0 (by dsimp only [old];omega)
  have Hrow d (hd : d∈List.range depth):
      nativeActualInitialRestThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) ≤
      nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st])+
        (eH d n+eG d n)*(M n).xs^3 := by
    let fd:Fin depth:=⟨d,List.mem_range.mp hd⟩
    have hsOld:retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))<U := by
      rw [←hindex];exact hs
    have hiOld:pre.length ≤ retainedMassPrefixIndex (w n).star.val (pre++(mid++tail)) := by
      rw [←hindex];omega
    have HM:partitionPoint 0 (pre++(mid++tail))
        (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))) ≤ A*W n := by
      rw [←hindex];exact HstarMass
    have HK:cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail))
        (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))) := by
      rw [←hindex];exact HstarK
    have BH0:=hjH fd pre.length U hiOld hsOld hU HcutLo HcutUp hmi HM HK 0
    have BG0:=hjG fd pre.length U hiOld hsOld hU HcutLo HcutUp hmi HM HK 0
    have BH:=native_actual_initial_category_bound_star_transport (M n) hsOld hs hU
      (by omega) hindex.symm BH0
    have BG:=native_actual_initial_category_bound_star_transport (M n) hsOld hs hU
      (by omega) hindex.symm BG0
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .jointLowTwoHigh|/
      (chi*K (pre.length+mid.length)) ≤ eH d n*((M n).xs*(M n).xs^2) at BH
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .fourGLowRestoration|/
      (chi*K (pre.length+mid.length)) ≤ eG d n*((M n).xs*(M n).xs^2) at BG
    rw [native_actual_initial_four_thermal_envelope_eq_two_add_joint_HIGH]
    nlinarith only [BH,BG]
  have Hsum:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right] at Hsum
  have Hsum':
      ((List.range depth).map (fun d=>nativeActualInitialRestThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum ≤
      ((List.range depth).map (fun d=>nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum+eJoint n*(M n).xs^3 := by
    simpa only [eJoint,List.sum_map_add] using Hsum
  apply HF.trans
  have Hpaid:=add_le_add_left Hsum'
    (Ci*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid) pre.length+
      1/(dim n+1:ℕ))+eFour n*(M n).xs^3)
  convert Hpaid using 1 <;> dsimp only [st,old,U,as] <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_higher_Taylor_on_strong_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal Tstar Lwin Cwindow c0 c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) (_hmacro : 0 < Rmacro) (_hRhalf : Rmacro ≤ 1/2) (_hCx : 0 < Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (_hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialHigherTaylorOnStrongGivenCutsAlong depth A Ci err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Hshell := G.pullback
  obtain ⟨Ci,hCi,err,herr,Herr,H⟩:=actual_inherited_initial_higher_Taylor_category_modulus_along_of_pullback_clocks
    (Cs:=Ccal^2) depth Bclock Temp Cf A (A+1) A cK hTemp hCf hA0.le (by positivity) hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
    dim hdim M W hcanonical hWlim Hsource hcompare Hshell w hw
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let Cout:=Ci*Cerr+1
  have hCerr:0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have hCout:0 < Cout:=by dsimp only [Cout];positivity
  refine ⟨Cout,hCout,err,herr,Herr,?_⟩
  filter_upwards [H,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hmesh:=uniformMasses_mesh_tendsto.eventually (eventually_le_nhds (M n).hxs)
  filter_upwards [hn L us hus hret hmesh hstar,Hmesh] with jGrid hj hmeshFine
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,HcutLo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper:partitionPoint 0 as U ≤ A*W n:=(partitionPoint_mono as ho HUV.le).trans Houter
  intro pre mid tail hcut hindex hmid hmi
  have HI:pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU:U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  refine ⟨HI,HU,?_⟩
  intro seedMass
  have Hlow:partitionPoint 0 as (pre.length+1) ≤ (A+1)*(M n).xs:=
    actual_initial_successor_low_cut_mass_le hus hmeshFine hmi
  have Hraw:=hj pre.length (pre.length+1) U
    (by rw [←hindex];omega) hs hU HcutLo Hupper (by omega) (by omega)
    (by rw [←hindex];omega) Hlow hmi Hmass HstarK seedMass
  have hDi:0 ≤ nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ):=by
    dsimp only [nativeOriginalCutLowErrorRadius];positivity
  have HC:=mul_le_mul_of_nonneg_right (show Ci*Cerr ≤ Cout by dsimp only [Cout];linarith)
    (mul_nonneg (sq_nonneg (M n).xs) hDi)
  have Hmajor:=add_le_add_right HC (err n*(M n).xs^3)
  have Hraw': let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as pre.length (retainedMassPrefixIndex (w n).star.val as) seedMass
            (by dsimp only [as];rw [←hcut];simp only [List.length_append];omega)]) .higherTaylor|/(chi*K (retainedMassPrefixIndex (w n).star.val as)) ≤
        Cout*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
        err n*(M n).xs^3 := by
    apply Hraw.trans
    convert Hmajor using 1 <;> dsimp only [Cerr,as] <;> ring
  exact native_actual_initial_category_bound_partition_star_transport (M n) hs HI hU HU
    (by rw [←hcut];simp only [List.length_append];omega)
    (by simp only [List.length_append];omega) hcut.symm hindex.symm Hraw'

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_initial_joint_LOW_restoration_on_given_cuts_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cwindow c0 cFirst cK A : ℝ}
    (depth : ℕ) (hA : 0 < A) (hcK : 0 < cK)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialJointLowRestorationOnGivenCutsAlong depth A err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  exact actual_inherited_initial_joint_LOW_restoration_on_given_cuts_along
    depth hA hcK hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf dim hdim M W radius
    hcanonical hWlim Hsource w high outer hw Hcuts

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_selected_bad_history_initial_full_source_modulus_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A Tstar Lwin Cwindow Cj Rmacro Cx : ℝ}
    (depth : ℕ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 < saving) (hCj : 0 ≤ Cj)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w)
    (HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃Ci : ℝ,0 ≤ Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialResidualFullModulusOnStrongCutsAlong depth A Ci err M W w high outer := by
  have hTemp : 0 ≤ Temp := G.hT.le
  classical
  obtain ⟨Ci,hCi,eTwo,heTwo,hTwoLim,HTwo⟩:=actual_selected_bad_history_initial_residual_two_thermal_modulus_along_comparable_context (c0:=c0)
    depth hmacro hRhalf hCx hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0
    hmargin hcapmargin hdim M G W radius hcanonical hWlim
    hcompare saving hsaving hCj w high outer hw Hsquare HJ Hmixed Hcuts
  have Hhigher d:=actual_selected_bad_history_initial_higher_Taylor_on_strong_given_cuts_along_comparable_context (c0:=c0)
    d hA hcK hc hcouter hmacro hRhalf hCx hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0
    hmargin hcapmargin hdim M G W radius
    hcanonical hWlim (Eventually.of_forall hcompare) w high outer hw Hcuts
  have Hjoint d:=actual_selected_bad_history_initial_joint_LOW_restoration_on_given_cuts_along_comparable_context (c0:=c0)
    d (zero_lt_one.trans_le hA) hcK hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hmargin hcapmargin
    dim hdim M G W radius hcanonical hWlim
    w high outer hw (Hcuts.mono fun _ hn=>hn.toActualSharpSourceCutGeometry)
  choose C hC eH heH hHlim HH using Hhigher
  choose eJ heJ hJlim HJlow using Hjoint
  let Csum:=((List.range depth).map C).sum
  have hCsum:0 ≤ Csum:=List.sum_nonneg (by
    intro a ha
    obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
    exact (hC d).le)
  let eRest n:=((List.range depth).map (fun d=>eH d n+eJ d n)).sum
  have heRest n:0 ≤ eRest n:=List.sum_nonneg (by
    intro a ha
    obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
    exact add_nonneg (heH d n) (heJ d n))
  have Hlim (ls : List ℕ):Tendsto (fun n=>(ls.map (fun d=>eH d n+eJ d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using ((hHlim d).add (hJlim d)).add ih
  refine ⟨Ci+Csum,add_nonneg hCi hCsum,(fun n=>eTwo n+eRest n),
    (fun n=>add_nonneg (heTwo n) (heRest n)),
    by simpa only [zero_add] using hTwoLim.add (Hlim (List.range depth)),?_⟩
  have HN:=Filter.eventually_all.mpr (fun d : Fin depth=>(HH d.val).and (HJlow d.val))
  filter_upwards [HTwo,HN] with n hnTwo hn
  intro L us hus hret hmesh hstar hhigh houter hnodes
  have Hgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>
    (hn d).1 L us hus hret hmesh hstar hhigh houter hnodes |>.and
      ((hn d).2 L us hus hret hmesh hstar hhigh houter))
  filter_upwards [hnTwo L us hus hret hmesh hstar hhigh houter hnodes,Hgrid] with jGrid hjTwo hj
  dsimp only at hjTwo hj ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  have hxW:(M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  intro pre mid tail hparts hindex hmid hmi
  obtain ⟨hs,hU,HT⟩:=hjTwo pre mid tail hparts hindex hmid hmi
  refine ⟨hs,hU,?_⟩
  have hHigher d:=(hj d).1 pre mid tail hparts hindex hmid hmi
  have hjJ d:=(hj d).2
  let old:=pre++(mid++tail)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks old (relocatedClock U 0 K))).H 0 0
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old pre.length (pre.length+mid.length) 0 (by dsimp only [old];omega)
  let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
  have Hrow d (hd : d∈List.range depth):
      nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) ≤
      C d*(M n).xs^2*Di+(eH d n+eJ d n)*(M n).xs^3 := by
    let fd:Fin depth:=⟨d,List.mem_range.mp hd⟩
    obtain ⟨_,_,BH⟩:=hHigher fd
    have BH0:=BH 0
    have hsNat:retainedMassPrefixIndex (w n).star.val as<U:=by
      rw [←hindex];exact hs
    have hiNat:pre.length ≤ retainedMassPrefixIndex (w n).star.val as:=by
      rw [←hindex];omega
    have hUas:U ≤ as.length:=by dsimp only [as];rw [←hparts];exact hU
    have BJ0:=hjJ fd pre.length hiNat hsNat hUas (M n).xs le_rfl hxW hmi 0
    have BJ:=actual_initial_seed_function_reindex as old hparts
      (retainedMassPrefixIndex (w n).star.val as) (pre.length+mid.length) hindex
      hiNat hsNat hUas (by omega) hs hU
      (fun bs st hs' hU' rows=>
        |nativeActualFourOtherCategorySum (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs' hU' (W n) d rows) .jointLowRestoration|/
        ((scalarTerminal.schedule (scalarBoundaryClocks bs (relocatedClock U 0
          (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf bs)))).H 0 0*
            nativeContinuumMixedClock (dim n) (M n).bf (M n).hf bs st))
      (eJ d n*(M n).xs*(M n).xs^2) BJ0
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .higherTaylor|/
      (chi*K (pre.length+mid.length)) ≤ C d*(M n).xs^2*Di+eH d n*(M n).xs^3 at BH0
    change |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]) .jointLowRestoration|/
      (chi*K (pre.length+mid.length)) ≤ eJ d n*(M n).xs*(M n).xs^2 at BJ
    simp only [nativeActualInitialTwoThermalCategoryEnvelope,nativeActualInitialTwoThermalSourceCategories,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    change _+_ ≤ _
    nlinarith only [BH0,BJ]
  have Hsum:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right] at Hsum
  have Hsum':
      ((List.range depth).map (fun d=>nativeActualInitialTwoThermalCategoryEnvelope (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum ≤
      Csum*(M n).xs^2*Di+eRest n*(M n).xs^3:=by
    simpa only [Csum,eRest,List.sum_map_add] using Hsum
  apply HT.trans
  have Hpaid:=add_le_add_left Hsum' (Ci*(M n).xs^2*Di+eTwo n*(M n).xs^3)
  convert Hpaid using 1 <;> dsimp only [Di,st,old,U,as] <;> ring

end OAI.SKFluctuations.Cavity

open Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_mean_transport_vanishing_along_comparable_context
    (Bclock Temp Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut) (houter : 0 < Couter)
    {m delta cl cu Az C0 Ct D Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U V : ℕ,i<U → U ≤ V → V ≤ as.length →
          partitionPoint 0 as i ≤ Ccut*x n →
          partitionPoint 0 as V ≤ Couter*(M n).canonicalDirectTestBandScale →
          abs (nativeActualTargetMeanTransportError (M n) as i U V) ≤ eta n*(x n)^3 := by
  obtain ⟨Cf,hCf,Hsource⟩ := NativeOverlapMinimum.actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M G
  obtain ⟨eta,heta,Heta,Hrate⟩ :=
    actual_selected_bad_history_target_G_cut_comparison_vanishing_envelope_along_comparable_context (c0:=c0)
      Bclock Temp Ccut Couter hTemp hCcut houter hm hdelta hroom hcl hcu hAz hC0 hCt
      hCs hc0 hmargin hcapmargin dim hdim M G
      x hxs hxlim hsmall hWlim
  refine ⟨fun n=>2*Temp*eta n,fun n=>mul_nonneg (mul_nonneg (by norm_num) hTemp) (heta n),?_,?_⟩
  · simpa only [mul_zero] using Heta.const_mul (2*Temp)
  · filter_upwards [Hsource,Hrate] with n hn hrate
    intro L us hus hret hmesh
    filter_upwards [hrate L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro i U V hi hUV hV hmass hVmass
    have HH:=hj i U V hi hUV hV hmass hVmass
    have Hbound:=actual_inherited_target_mean_transport_error_bound
      (M n) Temp Cf hTemp hn (finiteCutMasses us jGrid)
      (finiteCutMasses_ordered us hus jGrid) i U V hi (hUV.trans hV)
    have hT : (0:ℝ)≤2*Temp := mul_nonneg (by norm_num) hTemp
    have HC:=mul_le_mul_of_nonneg_left HH.1 hT
    exact Hbound.trans (by simpa only [mul_assoc] using HC)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_mean_correction_vanishing_along_comparable_context
    (Bclock Temp Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U : ℕ,i<U → U ≤ as.length → partitionPoint 0 as i ≤ Ccut*x n →
          |nativeActualTargetOriginalMeanCorrection (M n) as i U| ≤ eta n*(x n)^3 := by
  obtain ⟨Cf,hCf,Hsource⟩ := NativeOverlapMinimum.actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M G
  have Htotal:=NativeOverlapMinimum.actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0)
    dim M G
  obtain ⟨C,hC,Hrate⟩:=eventually_actual_inherited_target_mean_correction_rate
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨fun n=>C*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6),fun n=>by positivity,?_,?_⟩
  · have H:=((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/6)).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)).const_mul C
    simpa only [Function.comp_def,mul_zero,neg_div] using H
  · have HX:=hxlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
    filter_upwards [hdim.eventually Hrate,Hsource,Htotal,HX] with n hn hs ht hx
    intro us hus
    filter_upwards [hn (M n) hs ht.1 ht.2 ((hxs n).trans hx) us hus] with jGrid hj
    dsimp only at hj ⊢
    intro i U hi hU hmass
    exact hj i U hi hU (x n) (hxs n) hmass

end OAI.SKFluctuations.Cavity

open Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_mean_reduction_along_comparable_context
    (Bclock Temp Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut) (houter : 0 < Couter)
    {m delta cl cu Az C0 Ct D Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U V : ℕ,i<U → U ≤ V → V ≤ as.length →
          partitionPoint 0 as i ≤ Ccut*x n →
          partitionPoint 0 as V ≤ Couter*(M n).canonicalDirectTestBandScale →
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          abs (nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as i-
            nativeOriginalScalarPairMean as K i-
            2*((M n).bf (partitionPoint 0 as i):ℝ)*chi*nativeActualTargetLongitudinalResponse (M n) as i V-
            nativeActualTargetOriginalTaylorPart (M n) as i U) ≤ eta n*(x n)^3 := by
  obtain ⟨etaT,hetaT,HetaT,HT⟩:=actual_selected_bad_history_target_mean_transport_vanishing_along_comparable_context (c0:=c0)
    Bclock Temp Ccut Couter hTemp hCcut houter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc0 hmargin hcapmargin dim hdim M G
    x hxs hxlim hsmall hWlim
  obtain ⟨etaM,hetaM,HetaM,HM⟩:=actual_selected_bad_history_target_mean_correction_vanishing_along_comparable_context (c0:=c0)
    Bclock Temp Ccut hTemp hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim M G x hxs hxlim
  refine ⟨fun n=>etaM n+etaT n,fun n=>add_nonneg (hetaM n) (hetaT n),?_,?_⟩
  · simpa only [add_zero] using HetaM.add HetaT
  · filter_upwards [HT,HM] with n hnT hnM
    intro L us hus hret hmesh
    filter_upwards [hnT L us hus hret hmesh,hnM us hus] with jGrid hjT hjM
    dsimp only at hjT hjM ⊢
    intro i U V hi hUV hV hmass hVmass
    have H:=actual_target_mean_eq_correction_response_transport_taylor
      (M n) (finiteCutMasses us jGrid) i U V hi (hUV.trans hV)
      (finiteCutMasses_ordered us hus jGrid)
    dsimp only at H
    rw [H]
    rw [show nativeActualTargetOriginalMeanCorrection (M n) (finiteCutMasses us jGrid) i U+
        2*((M n).bf (partitionPoint 0 (finiteCutMasses us jGrid) i):ℝ)*
          (scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us jGrid)
            (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid))))).H 0 0*
          nativeActualTargetLongitudinalResponse (M n) (finiteCutMasses us jGrid) i V+
        nativeActualTargetMeanTransportError (M n) (finiteCutMasses us jGrid) i U V+
        nativeActualTargetOriginalTaylorPart (M n) (finiteCutMasses us jGrid) i U-
        2*((M n).bf (partitionPoint 0 (finiteCutMasses us jGrid) i):ℝ)*
          (scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us jGrid)
            (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid))))).H 0 0*
          nativeActualTargetLongitudinalResponse (M n) (finiteCutMasses us jGrid) i V-
        nativeActualTargetOriginalTaylorPart (M n) (finiteCutMasses us jGrid) i U=
        nativeActualTargetOriginalMeanCorrection (M n) (finiteCutMasses us jGrid) i U+
        nativeActualTargetMeanTransportError (M n) (finiteCutMasses us jGrid) i U V by ring]
    have HB:=(abs_add_le _ _).trans (add_le_add
      (hjM i U hi (hUV.trans hV) hmass) (hjT i U V hi hUV hV hmass hVmass))
    exact HB.trans_eq (by ring)

end OAI.SKFluctuations.Cavity

open Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

private theorem target_scalar_approximation_triangle
    (s a gamma r t e d : ℝ) (H : |s-a-r-t|≤e) (HA : |a-gamma|≤d) :
    |s-gamma-r-t|≤e+d := by
  rw [show s-gamma-r-t=(s-a-r-t)+(a-gamma) by ring]
  exact (abs_add_le _ _).trans (add_le_add H HA)

theorem actual_selected_bad_history_continuum_target_mean_reduction_along_comparable_context
    (Bclock Temp Ccut Couter : ℝ)
    (hTemp : 0 < Temp) (hCcut : 0 ≤ Ccut) (houter : 0 < Couter)
    {m delta cl cu Az C0 Ct D Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀u∈us,let i:=retainedMassPrefixIndex u.val as
        ∀U V : ℕ,i<U → U ≤ V → V ≤ as.length → u.val ≤ Ccut*x n →
          partitionPoint 0 as V ≤ Couter*(M n).canonicalDirectTestBandScale →
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          abs (orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
            scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
              (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)-
            2*((M n).bf u.val:ℝ)*chi*nativeActualTargetLongitudinalResponse (M n) as i V-
            nativeActualTargetOriginalTaylorPart (M n) as i U) ≤ eta n*(x n)^3 := by
  obtain ⟨eta,heta,Heta,Hrate⟩:=actual_selected_bad_history_target_mean_reduction_along_comparable_context (c0:=c0)
    Bclock Temp Ccut Couter hTemp.le hCcut houter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc0 hmargin hcapmargin dim hdim M G
    x hxs hxlim hsmall hWlim
  have Htotal:=NativeOverlapMinimum.actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0)
    dim M G
  let e:=fun n=>((dim n+1:ℕ):ℝ)^(-(1:ℝ))
  have He : Tendsto e atTop (𝓝 0) := by
    have H:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)
    simpa only [Function.comp_def,e] using H
  refine ⟨fun n=>eta n+e n,fun n=>add_nonneg (heta n) (by dsimp only [e];positivity),?_,?_⟩
  · simpa only [add_zero] using Heta.add He
  · filter_upwards [Hrate,Htotal] with n hn ht
    refine ⟨ht.1,?_⟩
    intro L us hus hret hmesh
    have hx:=(M n).hxs.trans_le (hxs n)
    have Hscalar:=(M n).inherited_continuum_scalar_pair_errors_on_all_retained_masses
      hTemp ht.1 ht.2 us hus (e n*(x n)^3) (by dsimp only [e];positivity)
    filter_upwards [hn L us hus hret hmesh,Hscalar] with jGrid hj hscalar
    dsimp only at hj hscalar ⊢
    intro u hu U V hi hUV hV hmass hVmass
    let as:=finiteCutMasses us jGrid
    let i:=retainedMassPrefixIndex u.val as
    have ho:=finiteCutMasses_ordered us hus jGrid
    have Hret : partitionPoint 0 as i=u.val :=
      nativeRetainedCut_partitionPoint as ho u (finiteCutMasses_nodes us jGrid hu)
    have Hcenter : nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as i=
        orderedPathS (dim n+1) (M n).bf (M n).hf u.val := by
      have H:=native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone (partitionPoint_mem as ho i)
      rw [Hret] at H
      unfold nativePhysicalResourceCenter
      rw [Hret]
      exact H.symm
    have hmass' : partitionPoint 0 as i≤Ccut*x n := by rw [Hret];exact hmass
    have HB:=hj i U V hi hUV hV hmass' hVmass
    rw [Hcenter,Hret] at HB
    have HA:=target_scalar_approximation_triangle _ _ _ _ _ _ _ HB (hscalar u hu)
    exact HA.trans_eq (by ring)

end OAI.SKFluctuations.Cavity

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 5000000

theorem exists_actual_selected_bad_history_initial_residual_approx_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
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
  have hTemp : 0 < T := G.hT
  obtain ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,Hp,Hconstant⟩:=
    exists_actual_selected_bad_history_square_resource_pair_budgets_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Htotal:=actual_selected_bad_history_total_clock_and_root_comparable_context (c0:=c0)
    dim M G
  refine ⟨hs,Cf,hCf,Hsource,Cs,hCs,w,hw,Hsquare,Hmixed,Hsharp,Hp,Hconstant,?_⟩
  intro Cmass hCm
  exact exists_actual_same_star_initial_residual_approx_along
    hm hcu hAz hC0 (by linarith : 0≤T) hTemp hs Cmass dim hdim M W hxs hWlim
    (Htotal.mono fun _ h=>h.1) (Htotal.mono fun _ h=>h.2) w hw (Hp Cmass hCm)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem actual_second_low_actual_history_initial_mass_error_ratio_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ → ℝ) (hxsx : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (Couter : ℝ) (hCouter : 0 ≤ Couter) :
    Tendsto (fun n=>
      (∫u in 0..(Couter+1)*x n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(x n)^2) atTop (𝓝 0) := by
  have Hps := G.pullback
  have Hclock := G.pullback
  exact regular_minimum_initial_mass_error_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M x hxsx hxlim Hclock (Couter+1) (by linarith)

theorem actual_second_low_actual_history_sole_root_target_B0_modulus_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (Couter : ℝ) (hTemp : 0 ≤ Temp) (hCouter : 0 ≤ Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ → ℝ) (hxsx : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hxW : ∀ᶠn in atTop,x n ≤ (M n).canonicalDirectTestBandScale) :
    ∃(Cf C : ℝ) (eps : ℕ → ℝ),0 ≤ Cf ∧ 0 < C ∧ (∀n,0 ≤ eps n) ∧
      Tendsto eps atTop (𝓝 0) ∧
      ActualSecondLowOriginalSoleRootTargetB0ModulusOnEveryFinalNetAlong Couter Temp Cf C eps M x := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  obtain ⟨C,hC,HB⟩:=eventually_actual_minimum_inherited_second_low_sole_root_target_B0_integral_budget
    (D:=D) Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cerr:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp
  let I:=fun n=>(∫u in 0..(Couter+1)*x n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
    (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))
  let eps:=fun n=>C*Cerr*(I n/(x n)^2)
  have HCerr : 0 ≤ Cerr:=actualLowErrorComparisonConstant_nonneg _ hTemp
  have Hratio:=actual_second_low_actual_history_initial_mass_error_ratio_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G
    x hxsx hxlim Couter hCouter
  have Heps : Tendsto eps atTop (𝓝 0) := by
    have HH:=Hratio.const_mul (C*Cerr)
    simpa only [mul_zero] using HH
  have Hupper:=((hxlim.const_mul (Couter+1)).eventually
    (eventually_le_nhds (show (Couter+1)*(0:ℝ) < 1 by simp)))
  refine ⟨Cf,C,eps,hCf,hC,?_,Heps,?_⟩
  · intro n
    have hx : 0 < x n:=(M n).hxs.trans_le (hxsx n)
    have hI : 0 ≤ I n:=intervalIntegral.integral_nonneg (by positivity) (fun _ _=>Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg hC.le HCerr) (div_nonneg hI (sq_nonneg _))
  · filter_upwards [hdim.eventually HB,Hsource,hxW,Hupper] with n hn HS hband hupper
    have hx : 0 < x n:=(M n).hxs.trans_le (hxsx n)
    have hxs : (M n).xs ≤ 1:=by
      have hsmall : x n ≤ (Couter+1)*x n:=by nlinarith
      exact (hxsx n).trans (hsmall.trans hupper)
    intro L us hus hret hmesh
    filter_upwards [hn (M n) HS hxs L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro i U hU hi houter
    have HT:=hk i U (x n) hU hi (hxsx n) hband houter
    have hsmallBig : Couter*x n ≤ (Couter+1)*x n:=by nlinarith
    have hsmall : Couter*x n ≤ 1:=hsmallBig.trans hupper
    rw [min_eq_left hsmall] at HT
    have hiBig:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((native_comparison_thermal_intervalIntegrable (M n)).mono_set (by
        rw [uIcc_of_le (by positivity : 0 ≤ (Couter+1)*x n),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hupper))
    have Hmono : (∫u in 0..Couter*x n,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)) ≤ I n := by
      apply intervalIntegral.integral_mono_interval le_rfl (mul_nonneg hCouter hx.le) hsmallBig
        (ae_of_all _ (fun u=>Real.sqrt_nonneg _)) hiBig
    have Hcost:=mul_le_mul_of_nonneg_left Hmono (show 0 ≤ C*x n*Cerr by positivity)
    apply HT.trans
    apply (add_le_add le_rfl Hcost).trans
    have Heq : C*x n*Cerr*I n=eps n*(x n)^3:=by
      dsimp only [eps]
      field_simp
    exact le_of_eq (by rw [Heq])

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_original_Taylor_modulus_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Cs c0 c : ℝ}
    (Ccut : ℝ) (hTemp : 0≤Temp) (hCcut : 0≤Ccut)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCs : 0≤Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (x : ℕ→ℝ) (hxsx : ∀n,(M n).xs≤x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hxW : ∀ᶠn in atTop,x n≤(M n).canonicalDirectTestBandScale)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2≤Cs*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hW1 : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale≤1) :
    ∃(C : ℝ) (err : ℕ→ℝ),0<C ∧ (∀n,0≤err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤(M n).xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i U : ℕ),i<U → U≤as.length →
          2*c*x n≤partitionPoint 0 as U → partitionPoint 0 as U≤Ccut*x n →
          |nativeActualTargetOriginalTaylorPart (M n) as i U|≤
            C*(x n)^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
              1/(dim n+1:ℕ))+err n*(x n)^3 := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  have Hps := G.pullback
  have Hclock := G.pullback
  obtain ⟨C,hC,HC⟩:=eventually_actual_regular_target_original_Taylor_integral_budget
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let I:=fun n=>(∫u in 0..(Ccut+1)*x n,Real.sqrt
    (orderedPathB (dim n+1) (M n).bf (M n).hf u-(orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))
  let save:=fun n=>((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  let err:=fun n=>C*(I n/(x n)^2+save n)
  have HI:=actual_second_low_actual_history_initial_mass_error_ratio_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G
    x hxsx hxlim Ccut hCcut
  have HP : Tendsto save atTop (𝓝 0):=by
    have HH:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
      (by norm_num : (0:ℝ)<256))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [save,Function.comp_def] using HH
  have Herr : Tendsto err atTop (𝓝 0):=by
    have HH:=(HI.add HP).const_mul C
    simpa only [err,I,add_zero,mul_zero] using HH
  have Hupper:=((hxlim.const_mul (Ccut+1)).eventually
    (eventually_le_nhds (show (Ccut+1)*(0:ℝ)<1 by simp)))
  refine ⟨C,err,hC,?_,Herr,?_⟩
  · intro n
    have hx : 0<x n:=(M n).hxs.trans_le (hxsx n)
    have hI : 0≤I n:=intervalIntegral.integral_nonneg (by positivity) (fun _ _=>Real.sqrt_nonneg _)
    dsimp only [err,save]
    positivity
  · filter_upwards [hdim.eventually HC,Hsource,Hclock,hsmall,hW1,hxW,Hupper]
      with n hn hs hcN hsm hw hxw hupper
    have hx : 0<x n:=(M n).hxs.trans_le (hxsx n)
    have hcut1 : Ccut*x n≤1:=(by nlinarith : Ccut*x n≤(Ccut+1)*x n).trans hupper
    intro L us hus hret hmesh
    filter_upwards [hn (M n) hcN hs hsm hw L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro i U hi hU hcutlo hcut
    have H:=hj i U (x n) hi hU (hxsx n) hxw hcut1 hcutlo hcut
    have HIbig:=native_intervalIntegrable_sqrt_of_intervalIntegrable
      ((native_comparison_thermal_intervalIntegrable (M n)).mono_set (by
        rw [uIcc_of_le (by positivity : 0≤(Ccut+1)*x n),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hupper))
    have HImono : (∫u in 0..Ccut*x n,Real.sqrt
        (orderedPathB (dim n+1) (M n).bf (M n).hf u-(orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))≤I n:=
      intervalIntegral.integral_mono_interval le_rfl (mul_nonneg hCcut hx.le)
        (by nlinarith : Ccut*x n≤(Ccut+1)*x n) (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) HIbig
    apply H.trans
    have Hcost:=mul_le_mul_of_nonneg_left HImono (show 0≤C*x n by positivity)
    have HE : C*x n*I n+C*save n*(x n)^3=err n*(x n)^3:=by
      dsimp only [err]
      field_simp
    dsimp only [NativeOverlapContext.N] at Hcost ⊢
    dsimp only [save] at HE
    rw [←HE]
    nlinarith only [Hcost]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

private theorem target_gap_residual_triangle
    {S G a L R T C D x e t r A : ℝ} (_hx : 0 ≤ x) (_hr : 0 ≤ r)
    (Hm : |S-G-a*L-T| ≤ e*x^3) (HT : |T| ≤ C*x^2*D+t*x^3)
    (HR : |L-R| ≤ r*x^3) (Ha : |a| ≤ A) :
    |S-G-a*R| ≤ C*x^2*D+(e+t+A*r)*x^3 := by
  have Hprod : |a*(L-R)| ≤ A*(r*x^3) := by
    rw [abs_mul]
    exact mul_le_mul Ha HR (abs_nonneg _) (le_trans (abs_nonneg _) Ha)
  rw [show S-G-a*R=(S-G-a*L-T)+T+a*(L-R) by ring]
  have H:=((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add Hm HT) Hprod)
  exact H.trans_eq (by ring)

theorem actual_selected_bad_history_continuum_target_residual_modulus_of_initial_approx_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp Cs c0 c saving : ℝ}
    (Ccut Couter : ℝ) (hTemp : 0 < Temp) (hCcut : 0 ≤ Ccut) (hCouter : 0 < Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hsaving : 0 < saving) (depth : ℕ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (W x : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (hxsx : ∀n,(M n).xs ≤ x n)
    (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (Hresidual : ActualTargetInitialResidualApproxAlong depth saving Ccut M W w) :
    ∃(C : ℝ) (eta : ℕ→ℝ),0 < C ∧ (∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ActualContinuumTargetResidualModulusAlong hTemp depth Ccut Couter c C eta M W x w := by
  have hxlim : Tendsto x atTop (𝓝 0):=squeeze_zero'
    (Filter.Eventually.of_forall (fun n=>(M n).hxs.le.trans (hxsx n))) hxW hWlim
  have HWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    simpa only [←hcanonical] using hWlim
  have HxW : ∀ᶠn in atTop,x n ≤ (M n).canonicalDirectTestBandScale:=by
    simpa only [hcanonical] using hxW
  have HW1:=HWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks_comparable_context (c0:=c0)
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim M
    G
  obtain ⟨em,hem,Hem,HM⟩:=actual_selected_bad_history_continuum_target_mean_reduction_along_comparable_context (c0:=c0)
    Bclock Temp Ccut Couter hTemp hCcut hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc0 hmargin hcapmargin dim hdim M G
    x hxsx hxlim hsmall HWlim
  obtain ⟨C,et,hC,het,Het,HT⟩:=actual_selected_bad_history_target_original_Taylor_modulus_along_comparable_context (c0:=c0)
    Ccut hTemp.le hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter hc0
    hmargin hcapmargin dim hdim M G
    x hxsx hxlim HxW hsmall HW1
  let rate n:=((dim n+1:ℕ):ℝ)^(-saving)
  have Hrate : Tendsto rate atTop (𝓝 0):=by
    have H:=(tendsto_rpow_neg_atTop hsaving).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)
    simpa only [rate,Function.comp_def] using H
  let eta n:=em n+et n+6*Temp*rate n
  have Heta : Tendsto eta atTop (𝓝 0):=by
    simpa only [add_zero,mul_zero] using (Hem.add Het).add (Hrate.const_mul (6*Temp))
  refine ⟨C,eta,hC,?_,Heta,?_⟩
  · intro n
    have hr : 0 ≤ rate n:=Real.rpow_nonneg (by positivity) _
    have hm0:=hem n
    have ht0:=het n
    dsimp only [eta]
    positivity
  · filter_upwards [HM,HT,Hresidual,Hsource,hxW] with n hmN htN hrN hsource hxw
    obtain ⟨htotal,hmN⟩:=hmN
    refine ⟨htotal,?_⟩
    intro Lnet us hus hstar hret hmesh
    filter_upwards [hmN Lnet us hus hret hmesh,htN Lnet us hus hret hmesh,
      hrN Lnet us hus hstar hret hmesh] with jGrid hmj htj hrj
    dsimp only at hmj htj hrj ⊢
    intro u hu U V hi hiU hUV hs hV hcutlo hcut hVmass
    let as:=finiteCutMasses us jGrid
    let i:=retainedMassPrefixIndex u.val as
    let star:=retainedMassPrefixIndex (w n).star.val as
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hU:=hUV.trans hV
    have Hret : partitionPoint 0 as i=u.val:=nativeRetainedCut_partitionPoint as ho u
      (finiteCutMasses_nodes us jGrid hu)
    have himass : partitionPoint 0 as i ≤ Ccut*x n:=(partitionPoint_mono as ho hiU.le).trans hcut
    have hmass : u.val ≤ Ccut*x n:=by rw [←Hret];exact himass
    have HM:=hmj u hu U V hiU hUV hV hmass (by simpa only [←hcanonical n] using hVmass)
    have HT:=htj i U hiU hU hcutlo hcut
    have HR:=hrj V i hi hs hV (x n) (hxsx n) hxw himass
    have Hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid (M n) as ho U
      (Nat.zero_le i |>.trans_lt hiU) hU
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    have Hb:=hsource u.val ⟨u.property.le,hus u hu⟩
    have Ha : |2*((M n).bf u.val:ℝ)*chi| ≤ 2*Temp:=by
      have Hmul:=mul_le_mul Hb.1 Hchi.2 Hchi.1 hTemp.le
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) Hchi.1)]
      nlinarith only [Hmul]
    have H:=target_gap_residual_triangle ((M n).hxs.le.trans (hxsx n))
      (show 0 ≤ 3*rate n by dsimp only [rate];positivity) HM HT HR Ha
    exact H.trans_eq (by dsimp only [eta,rate];ring)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
set_option maxHeartbeats 8000000

theorem actual_selected_bad_history_scalar_gap_integral_saving_tendsto_zero_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (A C : ℝ) (hA : 0 < A) (err : ℕ → ℝ) (herrlim : Tendsto err atTop (𝓝 0)) :
    Tendsto (fun n=>(M n).originalScalarGapIntegralSaving A C (err n)) atTop (𝓝 0) := by
  have Hd := actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M G hsmall hWlim A hA
  have Hs := actual_scalar_gap_site_ratio_tendsto_zero_along hm hC0 dim hdim M hWlim
  have H := ((Hd.const_mul C).add (Hs.const_mul (C*A))).add (herrlim.const_mul A)
  simpa only [originalScalarGapIntegralSaving,mul_zero,add_zero,mul_one_div] using H

theorem actual_selected_bad_history_original_scalar_gap_integral_envelope_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (err : ℕ → ℝ) (herr : ∀n,0 ≤ err n) (herrlim : Tendsto err atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ, (∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀n (T : ℝ) (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
        (star : ℝ), star ∈ Icc (0:ℝ) 1 →
        (∀u,0 < u → u ≤ A*(M n).xs → u < star →
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
            ((M n).inheritedScalarMassProfile hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
          C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
            (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(M n).context.N)+
              err n*(M n).xs^3) →
        (∫u in 0..min (A*(M n).xs) star,
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
            ((M n).inheritedScalarMassProfile hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|) ≤ eta n*(M n).xs^4 := by
  refine ⟨fun n=>(M n).originalScalarGapIntegralSaving A C (err n),
    fun n=>(M n).originalScalarGapIntegralSaving_nonneg hA hC (herr n),
    actual_selected_bad_history_scalar_gap_integral_saving_tendsto_zero_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M G hsmall hWlim A C hA err herrlim, ?_⟩
  intro n T hT htotal star hstar hpoint
  exact (M n).actual_original_scalar_gap_before_star_integral_le
    hT htotal hA hC (herr n) hstar hpoint

theorem actual_selected_bad_history_original_scalar_gap_integral_ratio_tendsto_zero_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (err : ℕ → ℝ) (herr : ∀n,0 ≤ err n) (herrlim : Tendsto err atTop (𝓝 0))
    (hT : 0 < T) (htotal : ∀n u,u∈Icc (0:ℝ) 1 → (M n).h u+(M n).b u ≤ T)
    (star : ℕ → ℝ) (hstar : ∀n,star n ∈ Icc (0:ℝ) 1)
    (hpoint : ∀ᶠn in atTop,∀u,0 < u → u ≤ A*(M n).xs → u < star n →
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
        ((M n).inheritedScalarMassProfile hT (htotal n))
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
      C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(M n).context.N)+
          err n*(M n).xs^3) :
    Tendsto (fun n=>(∫u in 0..min (A*(M n).xs) (star n),
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
        ((M n).inheritedScalarMassProfile hT (htotal n))
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/(M n).xs^4) atTop (𝓝 0) := by
  obtain ⟨eta,heta,hetalim,H⟩ :=
    actual_selected_bad_history_original_scalar_gap_integral_envelope_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M G hsmall hWlim A C hA hC err herr herrlim
  apply squeeze_zero' _ _ hetalim
  · filter_upwards [] with n
    apply div_nonneg
    · exact intervalIntegral.integral_nonneg
        (le_min (mul_pos hA (M n).hxs).le (hstar n).1) (fun _ _ => abs_nonneg _)
    · exact pow_nonneg (M n).hxs.le 4
  · filter_upwards [hpoint] with n hn
    exact (div_le_iff₀ (pow_pos (M n).hxs 4)).mpr
      (H n T hT (htotal n) (star n) (hstar n) hn)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open LaplaceWindowFormalization NativeOverlapMinimum
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_covered_scalar_gap_integral_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare A C cFirst cK Acut Rmacro Cx : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare) (hTemp : 0 < Temp) (hA : 0 < A) (hC : 0 ≤ C)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M Temp)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (W radius : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK Acut Rmacro Cx)
    (Hcoverage : ∀ᶠn in atTop,A*(M n).xs ≤ (w n).star.val)
    (rate : ℕ→ℝ) (hrate : ∀n,0 ≤ rate n) (hratelim : Tendsto rate atTop (𝓝 0))
    (Hgap : ActualOriginalTargetScalarGapModulusAlong hTemp A C rate M w) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ActualOriginalScalarGapIntegralOnBandAlong hTemp A eta M := by
  obtain ⟨eta,heta,hetalim,Hintegral⟩:=
    actual_selected_bad_history_original_scalar_gap_integral_envelope_along_comparable_context (c0:=c0)
      hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim M G hsmall hWlim A C hA hC rate hrate hratelim
  refine ⟨eta,heta,hetalim,?_⟩
  filter_upwards [Hcuts,Hcoverage,Hgap] with n hnCuts hnCoverage hnGap
  obtain ⟨htotal,hnGap⟩:=hnGap
  refine ⟨htotal,?_⟩
  have hstar1 : (w n).star.val ≤ 1:=
    (hnCuts.star_lt.trans hnCuts.high_lt).le.trans hnCuts.outer_le_one
  have H:=Hintegral n Temp hTemp htotal (w n).star.val
    ⟨(w n).star.property.le,hstar1⟩ (by
      intro u hu huA hustar
      exact hnGap ⟨u,hu⟩ huA hustar)
  simpa only [min_eq_left hnCoverage] using H

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_original_scalar_gap_integral_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ActualOriginalScalarGapIntegralOnBandAlong
        (G.hT) Atarget eta M := by
  have hTemp : 0 < T := G.hT
  let cInner:=Atarget+1+2*cu*(Az+1)
  let Cinner:=2*cInner
  let Rmacro:ℝ:=1/4
  have hcbase : 0 ≤ 2*cu*(Az+1):=by positivity
  have hcInner : 0 < cInner:=by dsimp only [cInner];linarith
  have hcouter : 2*cu*(Az+1) ≤ cInner:=by dsimp only [cInner];linarith
  have hinner : 0 < Cinner:=by dsimp only [Cinner];positivity
  have hTargetInner : Atarget < 2*cInner:=by dsimp only [cInner];linarith
  have hmacro : 0 < Rmacro:=by norm_num [Rmacro]
  have hRhalf : Rmacro ≤ 1/2:=by norm_num [Rmacro]
  have hT : 0 < T:=G.hT
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hcoverage,
    Hsquare,Hmixed,_Hsharp,_Hconstant,_Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,_hKv,
    hFirst,hFirstLower,hcKcut,high,outer,_Hvalues,Hstrong,threshold,hthreshold,Hbootstrap⟩:=
    exists_actual_selected_bad_history_covered_target_initial_inputs_along_comparable_context (c0:=c0)
      Atarget hAtarget.le Rmacro Cinner hmacro hRhalf hinner
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  let Aouter:=max (Ku+1) Atarget
  have hAouter : 1 ≤ Aouter:=(by linarith : (1:ℝ) ≤ Ku+1).trans (le_max_left _ _)
  have hAo : 0 < Aouter:=zero_lt_one.trans_le hAouter
  have Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut Aouter Rmacro Cinner := by
    filter_upwards [Hstrong] with n hn
    exact hn.mono_outer_scale (hW n).le (le_max_left _ _)
  obtain ⟨thresholdI,_hthresholdI,savingI,hsavingI,HapproxI⟩:=Happrox Cinner hinner.le
  let depth:=max threshold thresholdI
  obtain ⟨Cj,hCj,HJ0⟩:=Hbootstrap depth (le_max_left _ _)
  have HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer := by
    filter_upwards [HJ0] with n hn
    intro Lnet us hus hret hmesh hstar hhigh houter hnodes
    filter_upwards [hn Lnet us hus hret hmesh hstar hhigh houter hnodes] with jGrid hj
    obtain ⟨_hs,_hU,_hcal,Hbond⟩:=hj
    exact Hbond
  obtain ⟨Cr,hCr,er,her,herlim,Hfull⟩:=actual_selected_bad_history_initial_full_source_modulus_along_comparable_context (c0:=c0)
    depth hmacro hRhalf hinner hAouter hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim M G W (fun n=>Kv*W n)
    hcanonical hWlim hcompare (actualSlowWindowExponent m delta/256) hsaving hCj.le
    w high outer hw Hsquare HJ Hmixed Hcuts
  have HfullTarget:=Hfull.to_retained_targets (show Atarget ≤ Aouter from le_max_right _ _)
  obtain ⟨Ctgt,et,hCtgt,het,hetlim,Htarget⟩:=
    actual_selected_bad_history_continuum_target_residual_modulus_of_initial_approx_comparable_context (c0:=c0)
      Cinner Aouter hT hinner.le hAo hm hdelta hroom hcl hcu hAz hC0 hCt
      (sq_nonneg Ccal) hcInner hcouter hc0 hmargin hcapmargin hsavingI depth dim hdim M
      G W (fun n=>(M n).xs) hcanonical hWlim
      (fun _=>le_rfl) (Eventually.of_forall hxs) (Eventually.of_forall hcompare) w
      (HapproxI depth (le_max_right _ _))
  obtain ⟨rate,hrate,hratelim,Hgap⟩:=actual_original_target_gap_from_full_residual_along
    hT depth Cinner hcInner le_rfl hTargetInner le_rfl M W (fun n=>Kv*W n) w high outer
    Hcuts Hsource et er hetlim herlim Htarget HfullTarget
  have hGapConstant : 0 ≤ Ctgt+2*T*Cr:=add_nonneg hCtgt.le
    (mul_nonneg (mul_nonneg (by norm_num) hT.le) hCr)
  have HWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have Hfun : (fun n=>(M n).canonicalDirectTestBandScale)=W:=
      funext (fun n=>(hcanonical n).symm)
    rw [Hfun]
    exact hWlim
  exact actual_selected_bad_history_covered_scalar_gap_integral_along_comparable_context (c0:=c0)
    hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hT hAtarget hGapConstant
    dim hdim M G (Eventually.of_forall hcompare) HWlim
    W (fun n=>Kv*W n) w high outer Hcuts (Hcoverage.mono (fun _ hn=>hn.le))
    rate hrate hratelim Hgap

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_original_scalar_gap_pointwise_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ rate : ℕ→ℝ,
      (∀n,0 ≤ rate n) ∧ Tendsto rate atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀u : ℝ, 0 < u → u ≤ Atarget*(M n).xs →
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-
            scalarCovarianceResponse (G.hT)
              ((M n).inheritedScalarMassProfile
                (G.hT) htotal)
              (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
          C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
            (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(dim n+1:ℕ))+
              rate n*(M n).xs^3 := by
  have hTemp : 0 < T := G.hT
  let cInner:=Atarget+1+2*cu*(Az+1)
  let Cinner:=2*cInner
  let Rmacro:ℝ:=1/4
  have hcbase : 0 ≤ 2*cu*(Az+1):=by positivity
  have hcInner : 0 < cInner:=by dsimp only [cInner];linarith
  have hcouter : 2*cu*(Az+1) ≤ cInner:=by dsimp only [cInner];linarith
  have hinner : 0 < Cinner:=by dsimp only [Cinner];positivity
  have hTargetInner : Atarget < 2*cInner:=by dsimp only [cInner];linarith
  have hmacro : 0 < Rmacro:=by norm_num [Rmacro]
  have hRhalf : Rmacro ≤ 1/2:=by norm_num [Rmacro]
  have hT : 0 < T:=G.hT
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hcoverage,
    Hsquare,Hmixed,_Hsharp,_Hconstant,_Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,_hKv,
    hFirst,hFirstLower,hcKcut,high,outer,_Hvalues,Hstrong,threshold,hthreshold,Hbootstrap⟩:=
    exists_actual_selected_bad_history_covered_target_initial_inputs_along_comparable_context (c0:=c0)
      Atarget hAtarget.le Rmacro Cinner hmacro hRhalf hinner
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  let Aouter:=max (Ku+1) Atarget
  have hAouter : 1 ≤ Aouter:=(by linarith : (1:ℝ) ≤ Ku+1).trans (le_max_left _ _)
  have hAo : 0 < Aouter:=zero_lt_one.trans_le hAouter
  have Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut Aouter Rmacro Cinner := by
    filter_upwards [Hstrong] with n hn
    exact hn.mono_outer_scale (hW n).le (le_max_left _ _)
  obtain ⟨thresholdI,_hthresholdI,savingI,hsavingI,HapproxI⟩:=Happrox Cinner hinner.le
  let depth:=max threshold thresholdI
  obtain ⟨Cj,hCj,HJ0⟩:=Hbootstrap depth (le_max_left _ _)
  have HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer := by
    filter_upwards [HJ0] with n hn
    intro Lnet us hus hret hmesh hstar hhigh houter hnodes
    filter_upwards [hn Lnet us hus hret hmesh hstar hhigh houter hnodes] with jGrid hj
    obtain ⟨_hs,_hU,_hcal,Hbond⟩:=hj
    exact Hbond
  obtain ⟨Cr,hCr,er,her,herlim,Hfull⟩:=actual_selected_bad_history_initial_full_source_modulus_along_comparable_context (c0:=c0)
    depth hmacro hRhalf hinner hAouter hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim M G W (fun n=>Kv*W n)
    hcanonical hWlim hcompare (actualSlowWindowExponent m delta/256) hsaving hCj.le
    w high outer hw Hsquare HJ Hmixed Hcuts
  have HfullTarget:=Hfull.to_retained_targets (show Atarget ≤ Aouter from le_max_right _ _)
  obtain ⟨Ctgt,et,hCtgt,het,hetlim,Htarget⟩:=
    actual_selected_bad_history_continuum_target_residual_modulus_of_initial_approx_comparable_context (c0:=c0)
      Cinner Aouter hT hinner.le hAo hm hdelta hroom hcl hcu hAz hC0 hCt
      (sq_nonneg Ccal) hcInner hcouter hc0 hmargin hcapmargin hsavingI depth dim hdim M
      G W (fun n=>(M n).xs) hcanonical hWlim
      (fun _=>le_rfl) (Eventually.of_forall hxs) (Eventually.of_forall hcompare) w
      (HapproxI depth (le_max_right _ _))
  obtain ⟨rate,hrate,hratelim,Hgap⟩:=actual_original_target_gap_from_full_residual_along
    hT depth Cinner hcInner le_rfl hTargetInner le_rfl M W (fun n=>Kv*W n) w high outer
    Hcuts Hsource et er hetlim herlim Htarget HfullTarget
  have hGapConstant : 0 ≤ Ctgt+2*T*Cr:=add_nonneg hCtgt.le
    (mul_nonneg (mul_nonneg (by norm_num) hT.le) hCr)
  refine ⟨Ctgt+2*T*Cr,hGapConstant,rate,hrate,hratelim,?_⟩
  filter_upwards [Hcoverage,Hgap] with n hncover hngap
  obtain ⟨htotal,hngap⟩:=hngap
  refine ⟨htotal,?_⟩
  intro u hu huA
  exact hngap ⟨u,hu⟩ huA (huA.trans_lt hncover)

end OAI.SKFluctuations.LaplaceWindowFormalization
