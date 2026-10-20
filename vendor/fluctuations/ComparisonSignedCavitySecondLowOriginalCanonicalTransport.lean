module

public import ComparisonSignedCavitySecondLowInitialPhysicalSource
public import ComparisonSignedCavityCanonicalMarkedOldProduct

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 30000000

def nativeSecondLowCanonicalOldShape {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n × Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) : ActualNaturalBoundaryShape n a t.tree :=
  (((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 s hs).retainOnMarked 0 t ht

theorem native_second_low_canonical_old_shape_source_mass
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n × Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) (e : Fin a) :
    (nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht).sourceLowMass e = G.sourceLowMass e := by
  simp only [nativeSecondLowCanonicalOldShape,ActualNaturalBoundaryShape.retained_source_mass]

theorem native_second_low_canonical_old_shape_rest_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n × Bool) as}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a → NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) (τ : t.tree.cavityLeft.Assignment) :
    ((nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht).canonicalMinimumSource M forms).restProduct τ =
      nativeSecondLowOldTest (G.canonicalMinimumSource M forms).restProduct p r s t τ := by
  simp only [nativeSecondLowCanonicalOldShape,ActualNaturalBoundaryShape.retained_canonical_restProduct,
    nativeSecondLowOldTest]

theorem native_second_low_four_mark_leaves_le {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n × Bool) as}
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) : t.tree.leaves ≤ T.leaves+4 := by
  have Hp := T.markedAttach_leaves 0 p hp
  have Hr := p.tree.markedAttach_leaves 0 r hr
  have Hs := r.tree.markedAttach_leaves 0 s hs
  have Ht := s.tree.markedAttach_leaves 0 t ht
  omega

end OAI.SKFluctuations.Cavity
