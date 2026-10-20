module

public import CavitySignedProjectedReplacement
public import CavityPhysicalFreshTooth

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalCenteredProjectedOverlap (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ)
    (center : ℝ) (σ : Spin n) : ℝ :=
  physicalProjectedBoundaryOverlap n steps σ x-center

theorem physical_centered_projected_difference_fresh (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ho : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (center : ℝ) (σ τ : Spin n) :
    physicalCenteredProjectedOverlap n steps x center σ-
      physicalCenteredProjectedOverlap n steps x center τ=
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun d=>orderedOverlap n σ d-orderedOverlap n τ d) steps x := by
  unfold physicalCenteredProjectedOverlap
  rw [sub_sub_sub_cancel_right]
  exact physical_projected_difference_eq_common_fresh_mean n steps ho σ τ x

theorem physical_weighted_target_functions (n : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (E U : ReplicaTree (FeatureIndex n) (Spin n) steps)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (Z : U.Assignment → ℝ) (old new : U.Assignment → Spin n) (x : FeatureIndex n → ℝ) :
    (E.fork U).expect (uniformWeight n) (finiteFeature n)
      (fun σ=>Z σ.2*H σ.1*(orderedOverlap n (old σ.2) (E.atSlot σ.1 s)-
        orderedOverlap n (new σ.2) (E.atSlot σ.1 s))) x=
    U.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>Z σ*inner ℝ (WithLp.toLp 2 (normalizedSpin n (old σ))-
        WithLp.toLp 2 (normalizedSpin n (new σ)))
        (physicalWeightedExteriorAnchor n E H s x)) x := by
  have he := E.weighted_exterior_average (uniformWeight n) (finiteFeature n) U H
    (fun σ=>WithLp.toLp 2 (normalizedSpin n (E.atSlot σ s))) Z
    (fun σ=>WithLp.toLp 2 (normalizedSpin n (old σ))-
      WithLp.toLp 2 (normalizedSpin n (new σ))) x
  simpa only [physicalWeightedExteriorAnchor,inner_sub_left,normalizedSpin_inner_eq_overlap] using he

theorem physical_signed_weighted_incoming_decomposition (n k : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (E : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (ho : OrderedSteps a steps)
    (g : ReplicaTree.MarkedPlacement (ReplicaTree.single (S := Spin n) steps) → ℝ)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (x : FeatureIndex n → ℝ) (center incomingCenter : ℝ) :
    let Y := physicalCenteredProjectedOverlap n steps x center
    (((ReplicaTree.single steps).markedAttach a).map fun p=>p.coeff*g p*
      (E.fork p.tree).expect (uniformWeight n) (finiteFeature n) (fun σ=>
        (Y (p.spin σ.2)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2)))*
          H σ.1*(orderedOverlap n
            (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2))
            (E.atSlot σ.1 s)-incomingCenter)*
          Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2))^k) x).sum=
    (1/2:ℝ)*
      ((((ReplicaTree.single steps).markedAttach a).map fun p=>p.coeff*g p*
        (E.fork p.tree).expect (uniformWeight n) (finiteFeature n) (fun σ=>
          (Y (p.spin σ.2)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2)))*
            H σ.1*(orderedOverlap n
              (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2))
              (E.atSlot σ.1 s)-incomingCenter)*
            (Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2))^k-
              Y (p.spin σ.2)^k)) x).sum+
      (((ReplicaTree.single steps).markedAttach a).map fun p=>p.coeff*g p*
        p.tree.expect (uniformWeight n) (finiteFeature n) (fun σ=>
          (Y (p.spin σ)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)))*
            Y (p.spin σ)^k*inner ℝ
              (WithLp.toLp 2 (normalizedSpin n
                (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)))-
                WithLp.toLp 2 (normalizedSpin n (p.spin σ)))
              (physicalWeightedExteriorAnchor n E H s x)) x).sum) := by
  dsimp only
  let Y := physicalCenteredProjectedOverlap n steps x center
  let P : E.Assignment → Spin n → ℝ := fun σ τ=>
    H σ*(orderedOverlap n τ (E.atSlot σ s)-incomingCenter)*Y τ^k
  have he := ReplicaTree.signed_single_projected_replacement (uniformWeight_pos n)
    (finiteFeature n) E ho g Y P x
  have hleft : (((ReplicaTree.single steps).markedAttach a).map fun p=>p.coeff*g p*
      (E.fork p.tree).expect (uniformWeight n) (finiteFeature n) (fun σ=>
        (Y (p.spin σ.2)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2)))*
          P σ.1 (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2))) x).sum=
    (((ReplicaTree.single steps).markedAttach a).map fun p=>p.coeff*g p*
      (E.fork p.tree).expect (uniformWeight n) (finiteFeature n) (fun σ=>
        (Y (p.spin σ.2)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2)))*
          H σ.1*(orderedOverlap n
            (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2))
            (E.atSlot σ.1 s)-incomingCenter)*
          Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ.2))^k) x).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    congr 1
    funext σ
    dsimp only [P]
    ring
  rw [hleft] at he
  rw [he]
  congr 1
  rw [←List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [←mul_add]
  congr 1
  have hin := physical_weighted_target_functions n E p.tree H s
    (fun σ=>(Y (p.spin σ)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)))*
      Y (p.spin σ)^k)
    (fun σ=>ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)) p.spin x
  rw [←hin,←ReplicaTree.expect_add]
  congr 1
  funext σ
  dsimp only [P]
  ring

end OAI.SKFluctuations
