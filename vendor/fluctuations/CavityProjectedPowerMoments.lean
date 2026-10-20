module

public import CavitySignedWeightedIncoming

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy

theorem physical_centered_projected_power_le_fresh (n m : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ho : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (center : ℝ) (σ : Spin n) :
    |physicalCenteredProjectedOverlap n steps x center σ|^m ≤
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun τ=>|orderedOverlap n σ τ-center|^m) steps x := by
  let T := ReplicaTree.single (S := Spin n) steps
  let F : T.Assignment → ℝ := fun τ=>
    orderedOverlap n σ (ReplicaTree.singleEquiv (S := Spin n) steps τ)-center
  have hJ := finite_weighted_mean_abs_pow_le
    (fun τ=>T.weight (uniformWeight n) (finiteFeature n) τ x) F
    (fun τ=>T.weight_nonneg (uniformWeight_pos n) (finiteFeature n) ho τ x)
    (T.weight_sum (uniformWeight_pos n) (finiteFeature n) ho x) m
  change |T.expect (uniformWeight n) (finiteFeature n) F x|^m ≤
    T.expect (uniformWeight n) (finiteFeature n) (fun τ=>|F τ|^m) x at hJ
  have hF : F=(fun τ=>orderedOverlap n σ
      (ReplicaTree.singleEquiv (S := Spin n) steps τ))+fun _=>(-center) := by
    funext τ
    dsimp only [F,Pi.add_apply]
    ring
  have hmean : T.expect (uniformWeight n) (finiteFeature n) F x=
      physicalCenteredProjectedOverlap n steps x center σ := by
    rw [hF]
    change T.expect (uniformWeight n) (finiteFeature n)
      (fun τ=>orderedOverlap n σ (ReplicaTree.singleEquiv (S := Spin n) steps τ)+(-center)) x=_
    rw [ReplicaTree.expect_add,T.expect_const (uniformWeight_pos n) (finiteFeature n) ho]
    dsimp only [T]
    rw [ReplicaTree.single_expect (uniformWeight_pos n) (finiteFeature n) steps ho
      (orderedOverlap n σ),
      ←physical_projected_overlap_eq_fresh_mean n steps ho]
    rfl
  rw [hmean] at hJ
  dsimp only [T,F] at hJ
  rw [ReplicaTree.single_expect (uniformWeight_pos n) (finiteFeature n) steps ho
    (fun τ=>|orderedOverlap n σ τ-center|^m)] at hJ
  exact hJ

theorem physical_projected_target_power_moment_le (n m : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (ho : OrderedSteps a steps) (s : T.Slot)
    (x : FeatureIndex n → ℝ) (center : ℝ) :
    T.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>|physicalCenteredProjectedOverlap n steps x center (T.atSlot σ s)|^m) x ≤
    levelPairMean (uniformWeight n) (finiteFeature n)
      (fun σ τ=>|orderedOverlap n σ τ-center|^m) steps 0 x := by
  have hp : T.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>|physicalCenteredProjectedOverlap n steps x center (T.atSlot σ s)|^m) x ≤
    T.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun τ=>|orderedOverlap n (T.atSlot σ s) τ-center|^m) steps x) x := by
    unfold ReplicaTree.expect
    apply Finset.sum_le_sum
    intro σ hσ
    exact mul_le_mul_of_nonneg_left
      (physical_centered_projected_power_le_fresh n m steps ho x center (T.atSlot σ s))
      (T.weight_nonneg (uniformWeight_pos n) (finiteFeature n) ho σ x)
  apply hp.trans_eq
  rw [T.expect_atSlot (uniformWeight_pos n) (finiteFeature n) ho s
    (fun σ=>gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun τ=>|orderedOverlap n σ τ-center|^m) steps x) x,
    ←hierarchyPairMean_eq_nested (uniformWeight_pos n) (finiteFeature n)
      (fun σ τ=>|orderedOverlap n σ τ-center|^m) steps ho]
  cases steps <;> rfl

end OAI.SKFluctuations
