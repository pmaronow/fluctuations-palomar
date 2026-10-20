module

public import ComparisonSignedCavityOriginalInheritedConstantEndpoints
public import ComparisonNativeActualSelectedBadHistoryReadout
public import ComparisonNativeActualHistoryCutoffSourceClocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_total_clock_and_root
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (dim : ℕ→ℕ)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T) ∧ (M n).h 0=0 := by
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  filter_upwards [Hps] with n hn
  exact (M n).actual_shell_history_total_root (ps.map (fun P=>P n)) hepsilon hn.2.1 hn.2.2

theorem actual_selected_bad_history_continuum_scalar_limits
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (dim : ℕ→ℕ)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hT : 0 < T)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T,
      (M n).h 0=0 ∧
      ∀(us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass),u∈us →
      Tendsto (fun k=>nativeOriginalScalarPairMean (finiteCutMasses us k)
        (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
        (𝓝 (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT htotal)
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
          scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val))) := by
  filter_upwards [actual_selected_bad_history_total_clock_and_root dim root M
    epsilon shell hepsilon hb hh Hhistory] with n hn
  refine ⟨hn.1,hn.2,?_⟩
  intro us hus u hu
  exact ⟨(M n).inherited_continuum_retained_scalar_pair_tendsto hT hn.1 hn.2 us hus u hu,
    (M n).inherited_continuum_retained_scalar_mean_gap_tendsto hT hn.1 hn.2 us hus u hu⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
