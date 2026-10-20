module

public import CavityExteriorResampling
public import CavityMomentAllocation
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalPinnedWindow

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalProjectedBoundaryOverlap (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (σ : Spin n)
    (x : FeatureIndex n → ℝ) : ℝ :=
  ∑ i, normalizedSpin n σ i*actualSpinMean n steps x i

theorem physical_projected_overlap_eq_fresh_mean (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ho : OrderedSteps a steps)
    (σ : Spin n) (x : FeatureIndex n → ℝ) :
    physicalProjectedBoundaryOverlap n steps σ x =
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (orderedOverlap n σ) steps x := by
  classical
  simp only [physicalProjectedBoundaryOverlap,actualSpinMean,
    gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) steps ho,
    orderedOverlap_normalized,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem physical_projected_factor_eq_fresh_fork (n : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (ho : OrderedSteps a steps) (P : T.Assignment → ℝ) (s : T.Slot)
    (h b : ℝ) (x : FeatureIndex n → ℝ) :
    T.expect (uniformWeight n) (finiteFeature n)
      (fun σ => P σ*(h+b*physicalProjectedBoundaryOverlap n steps (T.atSlot σ s) x)) x =
    (T.fork (ReplicaTree.single steps)).expect (uniformWeight n) (finiteFeature n)
      (fun σ => P σ.1*(h+b*orderedOverlap n (T.atSlot σ.1 s)
        (ReplicaTree.singleEquiv (S := Spin n) steps σ.2))) x := by
  rw [ReplicaTree.expect_fork]
  congr 1
  funext σ
  change P σ*(h+b*physicalProjectedBoundaryOverlap n steps (T.atSlot σ s) x) =
    (ReplicaTree.single steps).expect (uniformWeight n) (finiteFeature n)
      (fun τ => P σ*(h+b*orderedOverlap n (T.atSlot σ s)
        (ReplicaTree.singleEquiv (S := Spin n) steps τ))) x
  rw [ReplicaTree.expect_const_mul,ReplicaTree.expect_add,ReplicaTree.expect_const_mul,
    ReplicaTree.expect_const (uniformWeight_pos n) (finiteFeature n) _ ho,
    ReplicaTree.single_expect (uniformWeight_pos n) (finiteFeature n) steps ho,
    ← physical_projected_overlap_eq_fresh_mean n steps ho]

theorem physical_two_projected_factors_eq_fresh_forks (n : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (T : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (ho : OrderedSteps a steps) (P : T.Assignment → ℝ) (s t : T.Slot)
    (h₁ b₁ h₂ b₂ : ℝ) (x : FeatureIndex n → ℝ) :
    T.expect (uniformWeight n) (finiteFeature n)
      (fun σ => P σ*(h₁+b₁*physicalProjectedBoundaryOverlap n steps (T.atSlot σ s) x)*
        (h₂+b₂*physicalProjectedBoundaryOverlap n steps (T.atSlot σ t) x)) x =
    ((T.fork (ReplicaTree.single steps)).fork (ReplicaTree.single steps)).expect
      (uniformWeight n) (finiteFeature n)
      (fun σ => P σ.1.1*(h₁+b₁*orderedOverlap n (T.atSlot σ.1.1 s)
        (ReplicaTree.singleEquiv (S := Spin n) steps σ.1.2))*
        (h₂+b₂*orderedOverlap n (T.atSlot σ.1.1 t)
          (ReplicaTree.singleEquiv (S := Spin n) steps σ.2))) x := by
  calc
    _ = (T.fork (ReplicaTree.single steps)).expect (uniformWeight n) (finiteFeature n)
        (fun σ => P σ.1*(h₁+b₁*orderedOverlap n (T.atSlot σ.1 s)
          (ReplicaTree.singleEquiv (S := Spin n) steps σ.2))*
          (h₂+b₂*physicalProjectedBoundaryOverlap n steps (T.atSlot σ.1 t) x)) x := by
      convert physical_projected_factor_eq_fresh_fork n T ho
        (fun σ => P σ*(h₂+b₂*physicalProjectedBoundaryOverlap n steps (T.atSlot σ t) x))
        s h₁ b₁ x using 1 <;> congr 1 <;> funext σ <;> ring
    _ = _ := by
      exact physical_projected_factor_eq_fresh_fork n (T.fork (ReplicaTree.single steps)) ho
        (fun σ => P σ.1*(h₁+b₁*orderedOverlap n (T.atSlot σ.1 s)
          (ReplicaTree.singleEquiv (S := Spin n) steps σ.2))) (Sum.inl t) h₂ b₂ x

theorem physical_projected_difference_eq_common_fresh_mean (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ho : OrderedSteps a steps)
    (σ τ : Spin n) (x : FeatureIndex n → ℝ) :
    physicalProjectedBoundaryOverlap n steps σ x-physicalProjectedBoundaryOverlap n steps τ x =
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun d => orderedOverlap n σ d-orderedOverlap n τ d) steps x := by
  rw [physical_projected_overlap_eq_fresh_mean n steps ho,
    physical_projected_overlap_eq_fresh_mean n steps ho]
  simp only [gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) steps ho,
    sub_mul,Finset.sum_sub_distrib]

theorem physical_projected_difference_even_moment_le (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ho : OrderedSteps a steps)
    (σ τ : Spin n) (x : FeatureIndex n → ℝ) :
    |physicalProjectedBoundaryOverlap n steps σ x-
      physicalProjectedBoundaryOverlap n steps τ x|^(2*l) ≤
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
        (fun d => |orderedOverlap n σ d-orderedOverlap n τ d|^(2*l)) steps x := by
  let F := fun d : Spin n => orderedOverlap n σ d-orderedOverlap n τ d
  have hCS := (ReplicaTree.single steps).expect_mul_sq_le (uniformWeight_pos n)
    (finiteFeature n) ho (fun d => F (ReplicaTree.singleEquiv (S := Spin n) steps d))
    (fun _ => 1) x
  simp only [mul_one,one_pow,ReplicaTree.expect_const (uniformWeight_pos n) (finiteFeature n) _ ho,
    ReplicaTree.single_expect (uniformWeight_pos n) (finiteFeature n) steps ho] at hCS
  have hsingle : (ReplicaTree.single steps).expect (uniformWeight n) (finiteFeature n)
      (fun d => (F (ReplicaTree.singleEquiv (S := Spin n) steps d))^2) x =
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (fun d => (F d)^2) steps x :=
    ReplicaTree.single_expect (uniformWeight_pos n) (finiteFeature n) steps ho (fun d => (F d)^2) x
  rw [hsingle] at hCS
  have hpow := pow_le_pow_left₀ (sq_nonneg _) hCS l
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ho
  have hM : Measurable (fun p : ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length =>
      (F (ForwardPath.spin steps.length p))^2) :=
    ((measurable_of_countable F).comp (ForwardPath.spin_measurable _)).pow_const 2
  have hF : ∀ d, |F d| ≤ 2 := fun d => (abs_sub _ _).trans
    ((add_le_add (orderedOverlap_abs_le_one n σ d) (orderedOverlap_abs_le_one n τ d)).trans_eq
      (by norm_num))
  have H := bounded_integral_power_le (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps x)
    hM (fun _ => sq_nonneg _) (R := 4)
    (fun p => by simpa only [sq_abs,show (2:ℝ)^2=4 by norm_num] using
      pow_le_pow_left₀ (abs_nonneg _) (hF (ForwardPath.spin steps.length p)) 2) hl
  rw [integral_hierarchyPathKernel (uniformWeight_pos n) (finiteFeature n)
    (fun d => (F d)^2) steps ho x,
    integral_hierarchyPathKernel (uniformWeight_pos n) (finiteFeature n)
      (fun d => ((F d)^2)^l) steps ho x] at H
  rw [physical_projected_difference_eq_common_fresh_mean n steps ho]
  change |gaussianHierarchyMean (uniformWeight n) (finiteFeature n) F steps x|^(2*l) ≤ _
  rw [pow_mul,sq_abs]
  apply hpow.trans
  convert H using 1
  congr 1
  funext d
  change |F d|^(2*l) = ((F d)^2)^l
  rw [pow_mul,sq_abs]

end OAI.SKFluctuations
