module

public import ComparisonActualGeneralCanonicalResetProducts
public import ComparisonSignedCavityGeneratedMarkedReset

@[expose] public section
noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem retained_canonical_physical_restProduct
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm) (r : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach r) (σ : p.tree.cavityLeft.Assignment) :
    ((G.retainOnMarked r p hp).canonicalPhysicalSource bf hf f).restProduct σ=
      (G.canonicalPhysicalSource bf hf f).restProduct (p.restRestrict σ) := by
  rw [←(G.canonicalPhysicalSource bf hf f).retained_restProduct r p hp σ]
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalPhysicalSource,retainOnMarked,sourceLowMass,
    (T.markedAttach_embed_preserves r p hp).2]

end ActualNaturalBoundaryShape

theorem actual_general_generated_marked_canonical_rest_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (hi : i ≤ star) (hlen : star<as.length)
    (bf hf : ℝ→ℝ≥0)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (σ : p.tree.cavityLeft.Assignment) :
    (((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked r p hp).canonicalPhysicalSource bf hf
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j))
        (p.restRestrict σ) := by
  rw [ActualNaturalBoundaryShape.retained_canonical_physical_restProduct,
    actual_general_generated_complete_canonical_rest_product]

theorem actual_general_generated_marked_reset_change (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (ht : P.teeth=[])
    (hi : i ≤ star) (hlen : star<as.length) (e : T.Slot) (hIncoming : P.incoming=[e])
    (bf hf : ℝ→ℝ≥0)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (σ : p.tree.cavityLeft.Assignment) :
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    nativeRestGeneratedTestValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))-
      (((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked r p hp).canonicalPhysicalSource bf hf
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      (((nativeGeneratedExteriorShape n P hP hi hlen).retainOnMarked r p hp).canonicalPhysicalSource bf hf
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ*
      (R (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot p.mark))
          (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed e)))-
        R (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed P.target)))
          (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed e)))) := by
  dsimp only
  rw [actual_general_generated_marked_canonical_rest_product,
    native_rest_generated_reset_replace_sub P hP ht hi hlen,
    ActualNaturalBoundaryShape.retained_canonical_physical_restProduct,
    actual_general_generated_exterior_canonical_rest_product,hIncoming]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,p.restRestrict_at]
  rfl

end OAI.SKFluctuations.Cavity
