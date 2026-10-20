module

public import ComparisonSignedCavityActualAllocatedEndpoint
public import ComparisonSignedCavityActualFullSitePairAveraging
public import ComparisonSignedCavityOriginalEndpointMean
public import ComparisonNativeActualScalarPairLimit

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_original_rest_test_one (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) :
    nativeOriginalRestTestExpectation n q U b h K T (fun _=>1)=1 := by
  exact T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho
    0 (cutFullVariance n q U 1 1 b h K) 0

theorem native_original_site_pair_one_eq_physical (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (a z : T.Slot) (haz : a≠z) :
    nativeOriginalSitePairExpectation n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j))
      U b h K T (fun _=>1) a z=finitePhysicalMean (n+1) as b h (T.splitIndex a z) := by
  have H := native_actual_full_site_pair_eq_overlap T ho U b h K (fun _=>1)
    (by intro π σ;rfl) a z (Fin.last n)
  simp only [joinSpin_last,mul_one] at H
  have HM := fullEndpoint_overlap_mean_eq_physical n U b h K T ho a z haz
  unfold nativeOriginalSitePairExpectation
  simp only [one_mul,sitePair_apply]
  exact H.trans HM

theorem native_pure_scalar_endpoint_pair_eq_original (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (a z : T.Slot) (haz : a≠z) :
    nativePureScalarEndpointPair n q U b h K T a z=
      nativeOriginalScalarPairMean as K (T.splitIndex a z) := by
  have H := cutDisorderExpect_site_endpoint n q U 1 b h K T ho (sitePair T a z) 0
  simp only [map_zero,relocatedClock_one] at H
  have hh : T.cavityRightSlot a≠T.cavityRightSlot z :=
    fun h=>haz (T.cavityRightSlot.injective h)
  have HP := T.cavityRight.disorderExpect_pairAtSlot_actual
    (w := fun _ : Bool=>(1/2:ℝ)) (by intro σ;norm_num) scalarFeature ho
    0 (fun j _=>K j) 0 (T.cavityRightSlot a) (T.cavityRightSlot z) hh
    (fun σ τ=>spinValue σ*spinValue τ)
  rw [T.splitIndex_cavityRight] at HP
  have hunit (σ : Bool) : scalarFeature σ (fun _=>1)=spinValue σ := by
    cases σ <;> simp [scalarFeature,spinValue]
  have HP' : T.cavityRight.disorderExpect (fun _ : Bool=>(1/2:ℝ)) scalarFeature 0
      (fun j _=>K j) (sitePair T a z) 0=
      nativeOriginalScalarPairMean as K (T.splitIndex a z) := by
    dsimp only [nativeOriginalScalarPairMean,sitePair]
    simp_rw [hunit]
    exact HP
  exact H.trans HP'

theorem native_original_constant_endpoint_gap_eq_finite (n U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (a z : T.Slot) (haz : a≠z) :
    nativeOriginalSitePairExpectation n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j))
      U b h K T (fun _=>1) a z-
      nativePureScalarEndpointPair n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U b h K T a z=
      finitePhysicalMean (n+1) as b h (T.splitIndex a z)-
        nativeOriginalScalarPairMean as K (T.splitIndex a z) := by
  rw [native_original_site_pair_one_eq_physical n U b h K T ho a z haz,
    native_pure_scalar_endpoint_pair_eq_original n _ U b h K T ho a z haz]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open Hierarchy Cavity

theorem bare_retained_scalar_mean_gap_tendsto
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k =>
      finitePhysicalMean (n+1) (finiteCutMasses us k)
        (retainedStarMatrix M.bf (finiteCutMasses us k))
        (retainedStarField M.hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
      nativeOriginalScalarPairMean (finiteCutMasses us k)
        (retainedStarMixedClock n M.bf M.hf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (orderedPathS (n+1) M.bf M.hf u.val-
        scalarCovarianceResponse hT (M.bareScalarMassProfile hT hb hh)
          (actualMixedClock (n+1) M.bf M.hf u.val))) := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
    M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact (nativeRetainedFinitePhysicalMean_tendsto n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus u hu).sub
    (M.bare_retained_scalar_pair_tendsto hT hb hh us hus u hu)

end OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
