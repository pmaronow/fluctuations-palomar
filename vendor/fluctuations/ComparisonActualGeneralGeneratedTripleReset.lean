module

public import ComparisonActualGeneralTripleHighDynamicSource
public import ComparisonSignedCavityGeneratedTripleReset

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Classical
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_generated_triple_canonical_rest_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (hi : i ≤ star) (hlen : star < as.length)
    (bf hf : ℝ→ℝ≥0)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (σ : z.tree.cavityLeft.Assignment) :
    (((((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j))
        (p.restRestrict (r.restRestrict (z.restRestrict σ))) := by
  rw [ActualNaturalBoundaryShape.retained_canonical_physical_restProduct,
    ActualNaturalBoundaryShape.retained_canonical_physical_restProduct,
    actual_general_generated_marked_canonical_rest_product]

theorem actual_general_generated_triple_reset_change (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (ht : P.teeth=[])
    (hi : i ≤ star) (hlen : star < as.length) (e₀ : T.Slot) (hIncoming : P.incoming=[e₀])
    (bf hf : ℝ→ℝ≥0)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (σ : z.tree.cavityLeft.Assignment) :
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    nativeRestGeneratedTestValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target)
        (p.restRestrict (r.restRestrict (z.restRestrict σ)))
        (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed p.mark)))))-
      (((((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      (((((nativeGeneratedExteriorShape n P hP hi hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)).restProduct σ*
      (R (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed p.mark))))
          (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed e₀)))))-
        R (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed P.target)))))
          (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed e₀)))))) := by
  dsimp only
  simp only [ActualNaturalBoundaryShape.retained_canonical_physical_restProduct]
  have H:=actual_general_generated_marked_reset_change n P hP ht hi hlen e₀ hIncoming bf hf 0 p hp
    (r.restRestrict (z.restRestrict σ))
  simpa only [ActualNaturalBoundaryShape.retained_canonical_physical_restProduct,
    MarkedPlacement.restSpin,r.restRestrict_at,z.restRestrict_at] using H

end OAI.SKFluctuations.Cavity
