module

public import ComparisonSignedCavityActualObservedProjectionFactorization
public import ComparisonSignedCavityPhysicalProjectionFactorization

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass}

def nativeRestGeneratedExteriorValue (T : ClockTree (S×B) as) (P : NativeGeneratedTest T)
    (R : S→S→ℝ) (C : ℕ→ℝ) (σ : T.cavityLeft.Assignment) : ℝ :=
  (P.exterior.map (fun e=>R (T.cavityLeft.atSlot σ (T.cavityLeftSlot e.1))
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot e.2))-C (T.splitIndex e.1 e.2))).prod

def nativeRestGeneratedIncomingValue (T : ClockTree (S×B) as) (P : NativeGeneratedTest T)
    (R : S→S→ℝ) (C : ℕ→ℝ) (σ : T.cavityLeft.Assignment) : ℝ :=
  (P.incoming.map (fun c=>R (T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target))
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))-C (T.splitIndex P.target c))).prod

theorem native_rest_generated_reset_value {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) (ht : P.teeth=[]) (R : S→S→ℝ) (C : ℕ→ℝ)
    (σ : T.cavityLeft.Assignment) :
    nativeRestGeneratedTestValue T P R C σ=
      nativeRestGeneratedExteriorValue T P R C σ*nativeRestGeneratedIncomingValue T P R C σ := by
  simp only [nativeRestGeneratedTestValue,NativeGeneratedTest.edges,ht,List.map_nil,List.append_nil,
    List.map_append,List.prod_append,List.map_map,Function.comp_def,
    nativeRestGeneratedExteriorValue,nativeRestGeneratedIncomingValue]

variable [Nonempty B]

theorem native_rest_generated_exterior_value_eq_full {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) (R : S→S→ℝ) (C : ℕ→ℝ) (σ : T.Assignment) :
    nativeRestGeneratedExteriorValue T P R C (T.cavityAssignment σ).1=
      nativeGeneratedEdgeProduct T (fun u v=>R u.1 v.1) C P.exterior σ := by
  simp only [nativeRestGeneratedExteriorValue,nativeGeneratedEdgeProduct,T.atSlot_cavityLeft]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_exterior_canonical_rest_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    ((nativeGeneratedExteriorShape n P hP hi hstar).canonicalMinimumSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedExteriorValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ := by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=native_generated_exterior_canonical_product n P hP hi hstar M τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_exterior_value_eq_full]
  rw [ht,H]
  unfold nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
