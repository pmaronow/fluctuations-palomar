module

public import ComparisonSignedCavityOriginalConstantEndpoints
public import ComparisonNativeContinuumScalarPairLimit
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem continuum_retained_scalar_mean_gap_tendsto
    {T : ℝ} (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k=>
      finitePhysicalMean (n+1) (finiteCutMasses us k)
        (retainedStarMatrix bf (finiteCutMasses us k))
        (retainedStarField hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
      nativeOriginalScalarPairMean (finiteCutMasses us k)
        (nativeContinuumMixedClock n bf hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (orderedPathS (n+1) bf hf u.val-
        scalarCovarianceResponse hT (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal)
          (actualMixedClock (n+1) bf hf u.val))) :=
  (nativeRetainedFinitePhysicalMean_tendsto n bf hf hbf hhf us hus u hu).sub
    (continuum_retained_scalar_pair_tendsto n bf hf hbf hhf hroot hT htotal us hus u hu)

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_continuum_retained_scalar_pair_tendsto
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T)
    (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k=>nativeOriginalScalarPairMean (finiteCutMasses us k)
      (nativeContinuumMixedClock n M.bf M.hf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
        (actualMixedClock (n+1) M.bf M.hf u.val))) :=
  continuum_retained_scalar_pair_tendsto n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu

theorem inherited_continuum_retained_scalar_mean_gap_tendsto
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T)
    (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k=>
      finitePhysicalMean (n+1) (finiteCutMasses us k)
        (retainedStarMatrix M.bf (finiteCutMasses us k))
        (retainedStarField M.hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
      nativeOriginalScalarPairMean (finiteCutMasses us k)
        (nativeContinuumMixedClock n M.bf M.hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (orderedPathS (n+1) M.bf M.hf u.val-
        scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
          (actualMixedClock (n+1) M.bf M.hf u.val))) :=
  continuum_retained_scalar_mean_gap_tendsto n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem original_continuum_constant_endpoint_gap_tendsto
    {T : ℝ} (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us)
    (U : ℕ→ℕ) (V : (k:ℕ)→ClockTree (Spin n×Bool) (finiteCutMasses us k))
    (a z : (k:ℕ)→(V k).Slot) (haz : ∀k,a k≠z k)
    (hsplit : ∀k,(V k).splitIndex (a k) (z k)=retainedMassPrefixIndex u.val (finiteCutMasses us k)) :
    Tendsto (fun k=>
      let as:=finiteCutMasses us k
      let b:=retainedStarMatrix bf as
      let h:=retainedStarField hf as
      let K:=nativeContinuumMixedClock n bf hf as
      let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      nativeOriginalSitePairExpectation n q (U k) b h K (V k) (fun _=>1) (a k) (z k)-
        nativePureScalarEndpointPair n q (U k) b h K (V k) (a k) (z k)) atTop
      (𝓝 (orderedPathS (n+1) bf hf u.val-
        scalarCovarianceResponse hT (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal)
          (actualMixedClock (n+1) bf hf u.val))) := by
  apply (continuum_retained_scalar_mean_gap_tendsto n bf hf hbf hhf hroot hT htotal us hus u hu).congr'
  apply Eventually.of_forall
  intro k
  simpa only [hsplit k] using (native_original_constant_endpoint_gap_eq_finite n (U k)
    (retainedStarMatrix bf (finiteCutMasses us k)) (retainedStarField hf (finiteCutMasses us k))
    (nativeContinuumMixedClock n bf hf (finiteCutMasses us k)) (V k)
    (finiteCutMasses_ordered us hus k) (a k) (z k) (haz k)).symm

end OAI.SKFluctuations.Cavity
