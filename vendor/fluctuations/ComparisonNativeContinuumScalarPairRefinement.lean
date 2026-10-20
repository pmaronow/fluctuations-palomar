module

public import ComparisonSignedCavityOriginalInheritedConstantEndpoints

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity Filter Set
open scoped Topology NNReal

theorem continuum_retained_scalar_pair_error_eventually
    {T : ℝ} (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (hroot : hf 0=0) (hT : 0 < T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤T)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (u : PositiveMass) (hu : u∈us)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠk in atTop,
      |nativeOriginalScalarPairMean (finiteCutMasses us k)
          (nativeContinuumMixedClock n bf hf (finiteCutMasses us k))
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
        scalarCovarianceResponse hT
          (actualMixedMassProfile hT (n+1) (by omega) bf hf hbf hhf htotal)
          (actualMixedClock (n+1) bf hf u.val)|≤eps := by
  have H:=continuum_retained_scalar_pair_tendsto n bf hf hbf hhf hroot hT htotal us hus u hu
  filter_upwards [(Metric.tendsto_nhds.mp H) eps heps] with k hk
  simpa only [Real.dist_eq] using hk.le

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_continuum_retained_scalar_pair_error_eventually
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T) (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (u : PositiveMass) (hu : u∈us)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠk in atTop,
      |nativeOriginalScalarPairMean (finiteCutMasses us k)
          (nativeContinuumMixedClock n M.bf M.hf (finiteCutMasses us k))
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
        scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
          (actualMixedClock (n+1) M.bf M.hf u.val)|≤eps :=
  continuum_retained_scalar_pair_error_eventually n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu eps heps

theorem inherited_continuum_scalar_pair_errors_on_all_retained_masses
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T) (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val≤1) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠk in atTop,∀u∈us,
      |nativeOriginalScalarPairMean (finiteCutMasses us k)
          (nativeContinuumMixedClock n M.bf M.hf (finiteCutMasses us k))
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
        scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
          (actualMixedClock (n+1) M.bf M.hf u.val)|≤eps := by
  have Hfin (vs : List PositiveMass) (hvs : ∀u∈vs,u∈us) :
      ∀ᶠk in atTop,∀u∈vs,
        |nativeOriginalScalarPairMean (finiteCutMasses us k)
            (nativeContinuumMixedClock n M.bf M.hf (finiteCutMasses us k))
            (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
          scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
            (actualMixedClock (n+1) M.bf M.hf u.val)|≤eps := by
    induction vs with
    | nil=>exact Eventually.of_forall (by simp)
    | cons v vs ih=>
      have Hv:=M.inherited_continuum_retained_scalar_pair_error_eventually hT htotal hroot
        us hus v (hvs v (List.mem_cons_self)) eps heps
      have Hvs:=ih (by intro u hu;exact hvs u (List.mem_cons_of_mem v hu))
      filter_upwards [Hv,Hvs] with k hkv hkvs
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hkv
      · exact hkvs u hu
  exact Hfin us (fun _ hu=>hu)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
