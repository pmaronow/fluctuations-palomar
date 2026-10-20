module

public import ComparisonNativeActualRegularHighMassPhysicalBand
public import ComparisonNativeActualRegularIntermediateMassPhysicalDyad
public import ComparisonNativeActualRegularSampledHighTailSecond
public import ComparisonNativeActualRegularLowErrorDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

theorem eventually_actual_shell_history_strong_high_mass_dyad
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,a.b u=historyMatrixClock T epsilon shell ts u) →
        (∀u,a.h u=historyFieldClock ts u) →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
        ∀v : ℝ,0 < v → 2*v ≤ 1 → c*a.canonicalDirectTestBandScale ≤ v →
          (∫u in v..2*v,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/
            (a.xs^4*v/a.canonicalDirectTestBandScale^2) ≤
              a.context.N^(-(actualMassSavingExponent m delta/2)) := by
  filter_upwards [eventually_actual_regular_strong_high_mass_dyad (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter] with n hn
  intro a T epsilon shell ts hb hh
  exact hn a (NativePullbackClockRegularity.of_shell_history
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha
    T epsilon shell ts a.b a.h hb hh le_rfl zero_le_one le_rfl)

theorem eventually_actual_shell_history_strong_high_mass_band
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs A B : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hA : 0 < A) (hAB : A ≤ B) (houter : 2*cu*(Az+1) ≤ A) :
    ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,a.b u=historyMatrixClock T epsilon shell ts u) →
        (∀u,a.h u=historyFieldClock ts u) →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 → 2*B*a.canonicalDirectTestBandScale ≤ 1 →
        (∫u in A*a.canonicalDirectTestBandScale..B*a.canonicalDirectTestBandScale,
          orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2) ≤
          a.context.N^(-(3*actualMassSavingExponent m delta/8))*(a.xs^4/a.canonicalDirectTestBandScale) := by
  filter_upwards [eventually_actual_regular_strong_high_mass_band (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hA hAB houter] with n hn
  intro a T epsilon shell ts hb hh
  exact hn a (NativePullbackClockRegularity.of_shell_history
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha
    T epsilon shell ts a.b a.h hb hh le_rfl zero_le_one le_rfl)

theorem eventually_actual_shell_history_strong_intermediate_mass_dyad
    (C Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,a.b u=historyMatrixClock T epsilon shell ts u) →
        (∀u,a.h u=historyFieldClock ts u) →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
        ∀v : ℝ,0 < v → 2*v ≤ 1 → c*a.xs ≤ v → v ≤ C*a.canonicalDirectTestBandScale →
          (∫u in v..2*v,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)/
            (a.xs^4*v/(actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^2) ≤
              a.context.N^(-(actualMassSavingExponent m delta/2)) := by
  filter_upwards [eventually_actual_regular_strong_intermediate_mass_dyad (D:=D)
    C Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter] with n hn
  intro a T epsilon shell ts hb hh
  exact hn a (NativePullbackClockRegularity.of_shell_history
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha
    T epsilon shell ts a.b a.h hb hh le_rfl zero_le_one le_rfl)

theorem eventually_actual_shell_history_sampled_original_high_tail_second
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∀ᶠn : ℕ in atTop,
      ∀(a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,a.b u=historyMatrixClock T epsilon shell ts u) →
        (∀u,a.h u=historyFieldClock ts u) →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        ∀U : ℕ,U ≤ as.length → 2*c*a.canonicalDirectTestBandScale ≤ partitionPoint 0 as U →
          ClockTree.edgeBudget 0 as
            (fun k=>if k<U then 0 else (nativeOriginalCutLowErrorRadius n a.bf a.hf as k)^2) ≤
            a.context.N^(-(actualMassSavingExponent m delta/8))*
              (a.xs^4/a.canonicalDirectTestBandScale^2) := by
  filter_upwards [eventually_actual_regular_sampled_original_high_tail_second (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter] with n hn
  intro a T epsilon shell ts hb hh
  exact hn a (NativePullbackClockRegularity.of_shell_history
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha
    T epsilon shell ts a.b a.h hb hh le_rfl zero_le_one le_rfl)

namespace NativeOverlapMinimum

theorem actualOriginalLowErrorDensitySaving_shell_history_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (a : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn : ℕ in atTop,
      (a n).xs^2 ≤ Cs*laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs)
    (hWlim : Tendsto (fun n=>(a n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (T epsilon shell : ℕ→ℝ) (ts : ℕ→List ComparisonHistoryTerm)
    (hb : ∀n u,(a n).b u=historyMatrixClock (T n) (epsilon n) (shell n) (ts n) u)
    (hh : ∀n u,(a n).h u=historyFieldClock (ts n) u)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(a n).actualOriginalLowErrorDensitySaving C) atTop (𝓝 0) := by
  exact actualOriginalLowErrorDensitySaving_regular_tendsto_zero hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs a hsmall hWlim (fun n=>NativePullbackClockRegularity.of_shell_history
      (a n).context.hc (a n).context.hk (a n).context.hkc (a n).context.hm (a n).context.hM (a n).alpha
      (T n) (epsilon n) (shell n) (ts n) (a n).b (a n).h (hb n) (hh n)
      le_rfl zero_le_one le_rfl) C hC

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
