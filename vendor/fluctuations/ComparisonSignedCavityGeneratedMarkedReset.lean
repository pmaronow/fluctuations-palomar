module

public import ComparisonSignedCavityGeneratedCompleteShape
public import ComparisonSignedCavityOriginalPairedAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_marked_canonical_rest_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (hi : i ≤ star) (hlen : star<as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (σ : p.tree.cavityLeft.Assignment) :
    (((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked r p hp).canonicalMinimumSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j))
        (p.restRestrict σ) := by
  rw [ActualNaturalBoundaryShape.retained_canonical_restProduct,
    native_generated_complete_canonical_rest_product]

theorem native_generated_marked_reset_change (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (ht : P.teeth=[])
    (hi : i ≤ star) (hlen : star<as.length) (e : T.Slot) (hIncoming : P.incoming=[e])
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (σ : p.tree.cavityLeft.Assignment) :
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    nativeRestGeneratedTestValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))-
      (((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked r p hp).canonicalMinimumSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      (((nativeGeneratedExteriorShape n P hP hi hlen).retainOnMarked r p hp).canonicalMinimumSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ*
      (R (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot p.mark))
          (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed e)))-
        R (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed P.target)))
          (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed e)))) := by
  dsimp only
  rw [native_generated_marked_canonical_rest_product,
    native_rest_generated_reset_replace_sub P hP ht hi hlen,
    ActualNaturalBoundaryShape.retained_canonical_restProduct,
    native_generated_exterior_canonical_rest_product,hIncoming]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,p.restRestrict_at]
  rfl

end OAI.SKFluctuations.Cavity
