module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

public section

namespace SKConstants

open scoped BigOperators

variable {ι ρ H : Type*}
variable [Fintype ι] [LinearOrder ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def weightedColumnSum (X : ι → H) (a : ι → ℝ) (I : Finset ι) : H :=
  ∑ i ∈ I, a i • X i

def strictUpperGramForm (X Y : ι → H) (a b : ι → ℝ) : ℝ :=
  ∑ p ∈ (Finset.univ.filter fun p : ι × ι => p.1 < p.2),
    inner (𝕜 := ℝ) (a p.1 • X p.1) (b p.2 • Y p.2)

omit [Fintype ι] [LinearOrder ι] in
theorem rectangle_inner_factorization (X Y : ι → H) (a b : ι → ℝ)
    (L R : Finset ι) :
    (∑ p ∈ L ×ˢ R,
      inner (𝕜 := ℝ) (a p.1 • X p.1) (b p.2 • Y p.2)) =
      inner (𝕜 := ℝ) (weightedColumnSum X a L) (weightedColumnSum Y b R) := by
  rw [Finset.sum_product]
  simp only [weightedColumnSum, sum_inner, inner_sum]
  exact Finset.sum_comm

theorem strictUpperGramForm_eq_rectangle_sum
    (X Y : ι → H) (a b : ι → ℝ) (rects : Finset ρ)
    (left right : ρ → Finset ι)
    (hdisjoint : Set.PairwiseDisjoint (↑rects)
      (fun r => left r ×ˢ right r))
    (hcover : rects.biUnion (fun r => left r ×ˢ right r) =
      Finset.univ.filter (fun p : ι × ι => p.1 < p.2)) :
    strictUpperGramForm X Y a b =
      ∑ r ∈ rects,
        inner (𝕜 := ℝ) (weightedColumnSum X a (left r))
          (weightedColumnSum Y b (right r)) := by
  unfold strictUpperGramForm
  rw [← hcover, Finset.sum_biUnion hdisjoint]
  exact Finset.sum_congr rfl (fun r _ =>
    rectangle_inner_factorization X Y a b (left r) (right r))

theorem strictUpperGramForm_abs_le_rectangle_energy
    (X Y : ι → H) (a b : ι → ℝ) (rects : Finset ρ)
    (left right : ρ → Finset ι)
    (hdisjoint : Set.PairwiseDisjoint (↑rects)
      (fun r => left r ×ˢ right r))
    (hcover : rects.biUnion (fun r => left r ×ˢ right r) =
      Finset.univ.filter (fun p : ι × ι => p.1 < p.2)) :
    |strictUpperGramForm X Y a b| ≤
      Real.sqrt (∑ r ∈ rects, ‖weightedColumnSum X a (left r)‖ ^ 2) *
      Real.sqrt (∑ r ∈ rects, ‖weightedColumnSum Y b (right r)‖ ^ 2) := by
  rw [strictUpperGramForm_eq_rectangle_sum X Y a b rects left right hdisjoint hcover]
  calc
    |∑ r ∈ rects, inner (𝕜 := ℝ) (weightedColumnSum X a (left r))
        (weightedColumnSum Y b (right r))| ≤
        ∑ r ∈ rects, |inner (𝕜 := ℝ) (weightedColumnSum X a (left r))
          (weightedColumnSum Y b (right r))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ rects,
        ‖weightedColumnSum X a (left r)‖ * ‖weightedColumnSum Y b (right r)‖ := by
      exact Finset.sum_le_sum (fun r _ => abs_real_inner_le_norm _ _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt rects
      (fun r => ‖weightedColumnSum X a (left r)‖)
      (fun r => ‖weightedColumnSum Y b (right r)‖)

theorem rectangle_bound_explicit
    (X Y : ι → H) (a b : ι → ℝ) (rects : Finset ρ)
    (left right : ρ → Finset ι)
    (hdisjoint : Set.PairwiseDisjoint (↑rects)
      (fun r => left r ×ˢ right r))
    (hcover : rects.biUnion (fun r => left r ×ˢ right r) =
      Finset.univ.filter (fun p : ι × ι => p.1 < p.2)) :
    |∑ p ∈ (Finset.univ.filter fun p : ι × ι => p.1 < p.2),
      inner (𝕜 := ℝ) (a p.1 • X p.1) (b p.2 • Y p.2)| ≤
      Real.sqrt (∑ r ∈ rects, ‖∑ i ∈ left r, a i • X i‖ ^ 2) *
      Real.sqrt (∑ r ∈ rects, ‖∑ j ∈ right r, b j • Y j‖ ^ 2) := by
  simpa only [strictUpperGramForm, weightedColumnSum] using
    strictUpperGramForm_abs_le_rectangle_energy X Y a b rects left right hdisjoint hcover

end SKConstants
