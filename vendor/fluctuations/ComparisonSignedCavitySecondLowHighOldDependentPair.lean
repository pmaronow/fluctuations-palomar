module

public import ComparisonSignedCavitySecondLowHighFieldPairValue

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped BigOperators NNReal
variable {ι : Type*} {S : Type} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowHighOldDependentPair (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ)
    (u v : T.Assignment → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ((nativeHighMarkedRows T s star a).map fun p => p.coeff *
    ((nativeHighMarkedRows p.tree (p.embed s) star a).map fun r => r.coeff *
      r.tree.expect w φ q (fun σ =>
        let old := p.restrict (r.restrict σ)
        P old * (φ (p.spin (r.restrict σ)) (u old) * φ (r.spin σ) (v old))) x).sum).sum

omit [Nonempty S] in
private theorem native_second_low_clock_expect_finsetSum
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (q : ℕ → ι → ℝ≥0) {α : Type*}
    (is : Finset α) (P : α → T.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ => ∑ i ∈ is, P i σ) x =
      ∑ i ∈ is, T.expect w φ q (P i) x := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

omit [Nonempty S] in
theorem native_second_low_high_old_dependent_pair_eq_finite_original
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ)
    (u v : T.Assignment → ι → ℝ) (x : ι → ℝ) :
    nativeSecondLowHighOldDependentPair w φ T s star a q P u v x =
      ∑ old : T.Assignment, nativeSecondLowHighFieldPair w φ T s star a q
        (fun τ => if τ = old then P τ else 0) (u old) (v old) x := by
  have H (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      (fun σ : r.tree.Assignment =>
        let old := p.restrict (r.restrict σ)
        P old * (φ (p.spin (r.restrict σ)) (u old) * φ (r.spin σ) (v old))) =
      (fun σ => ∑ old ∈ (Finset.univ : Finset T.Assignment),
        (if p.restrict (r.restrict σ) = old then P (p.restrict (r.restrict σ)) else 0) *
          (φ (p.spin (r.restrict σ)) (u old) * φ (r.spin σ) (v old))) := by
    funext σ
    simp
  unfold nativeSecondLowHighOldDependentPair
  simp_rw [H,native_second_low_clock_expect_finsetSum,Finset.mul_sum,
    ReplicaTree.list_sum_finset_sum,Finset.mul_sum,ReplicaTree.list_sum_finset_sum]
  rfl

theorem native_second_low_high_old_dependent_pair_symm
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    (a : ℝ) (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ)
    (u v : T.Assignment → ι → ℝ) (x : ι → ℝ) :
    nativeSecondLowHighOldDependentPair w φ T s star a q P u v x =
      nativeSecondLowHighOldDependentPair w φ T s star a q P v u x := by
  rw [native_second_low_high_old_dependent_pair_eq_finite_original,
    native_second_low_high_old_dependent_pair_eq_finite_original]
  apply Finset.sum_congr rfl
  intro old _
  exact native_second_low_high_field_pair_symm hw φ T s star a ho q
    (fun τ => if τ = old then P τ else 0) (u old) (v old) x

end OAI.SKFluctuations.Hierarchy.ClockTree
