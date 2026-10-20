module

public import ComparisonSignedCavitySecondLowPowerPairSymmetry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ReplicaTree
open scoped BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowOldDependentMarkedPair
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (u v : T.Assignment → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ((T.markedAttach a).map fun p => p.coeff *
    ((p.tree.markedAttach a).map fun q => q.coeff *
      q.tree.expect w φ (fun σ =>
        let old := p.restrict (q.restrict σ)
        P old * (φ (p.spin (q.restrict σ)) (u old) * φ (q.spin σ) (v old))) x).sum).sum

omit [Nonempty S] in
theorem native_second_low_old_dependent_marked_pair_eq_finite_original
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (u v : T.Assignment → ι → ℝ) (x : ι → ℝ) :
    nativeSecondLowOldDependentMarkedPair w φ T a P u v x =
      ∑ old : T.Assignment, T.markedPairExpectation w φ a
        (fun τ => if τ = old then P τ else 0)
        (fun σ τ => φ σ (u old) * φ τ (v old)) x := by
  classical
  have H (p : MarkedPlacement T) (q : MarkedPlacement p.tree) :
      (fun σ : q.tree.Assignment =>
        let old := p.restrict (q.restrict σ)
        P old * (φ (p.spin (q.restrict σ)) (u old) * φ (q.spin σ) (v old))) =
      (fun σ => ∑ old ∈ (Finset.univ : Finset T.Assignment),
        (if p.restrict (q.restrict σ) = old then P (p.restrict (q.restrict σ)) else 0) *
          (φ (p.spin (q.restrict σ)) (u old) * φ (q.spin σ) (v old))) := by
    funext σ
    simp
  unfold nativeSecondLowOldDependentMarkedPair
  simp_rw [H,expect_finsetSum,Finset.mul_sum,list_sum_finset_sum,
    Finset.mul_sum,list_sum_finset_sum]
  rfl

theorem native_second_low_old_dependent_marked_pair_symm
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (u v : T.Assignment → ι → ℝ) (x : ι → ℝ) :
    nativeSecondLowOldDependentMarkedPair w φ T a P u v x =
      nativeSecondLowOldDependentMarkedPair w φ T a P v u x := by
  rw [native_second_low_old_dependent_marked_pair_eq_finite_original,
    native_second_low_old_dependent_marked_pair_eq_finite_original]
  apply Finset.sum_congr rfl
  intro old _
  exact native_second_low_marked_field_pair_symm hw φ T ha
    (fun τ => if τ = old then P τ else 0) (u old) (v old) x

end OAI.SKFluctuations.Hierarchy.ReplicaTree
