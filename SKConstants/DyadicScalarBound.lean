module

public import SKConstants.DyadicNorm
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

theorem strict_gram_inner_sum (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2 ^ r))) :
    inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      (strictUpperTruncation (X.transpose * Y)) b) =
      ∑ p ∈ (Finset.univ.filter fun p : Fin (2 ^ r) × Fin (2 ^ r) => p.1 < p.2),
        inner (𝕜 := ℝ) (a p.1 • Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X
          (EuclideanSpace.single p.1 (1 : ℝ)))
          (b p.2 • Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
            (EuclideanSpace.single p.2 (1 : ℝ))) := by
  rw [strictUpperTruncation_inner_eq]
  apply Finset.sum_congr rfl
  intro p _
  simp only [inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
    map_one, one_mul, matrix_column_apply, gram_column_inner, starRingEnd_apply, star_trivial]

theorem dyadic_strict_gram_bilinear_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2 ^ r))) :
    |inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      (strictUpperTruncation (X.transpose * Y)) b)| ≤
      dyadicMatrixSeminorm r a X * dyadicMatrixSeminorm r b Y := by
  have h := dyadic_rectangle_bound r
    (fun i => Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X (EuclideanSpace.single i (1 : ℝ)))
    (fun j => Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y (EuclideanSpace.single j (1 : ℝ))) a b
  rw [← strict_gram_inner_sum] at h
  simp_rw [matrix_projected_column_sum] at h
  have hl : Real.sqrt (∑ n : DyadicCore.Node r,
      ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X (coordinateProjection (dyadicLeft r n) a)‖ ^ 2) ≤
      dyadicMatrixSeminorm r a X := Real.sqrt_le_iff.mpr
        ⟨apply_nonneg _ _, dyadic_left_image_energy_le r X a⟩
  have hr : Real.sqrt (∑ n : DyadicCore.Node r,
      ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y (coordinateProjection (dyadicRight r n) b)‖ ^ 2) ≤
      dyadicMatrixSeminorm r b Y := Real.sqrt_le_iff.mpr
        ⟨apply_nonneg _ _, dyadic_right_image_energy_le r Y b⟩
  exact h.trans (mul_le_mul hl hr (Real.sqrt_nonneg _) (apply_nonneg _ _))

theorem diagonal_gram_inner_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℝ) (a b : EuclideanSpace ℝ ι) :
    inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (Matrix.diagonal (fun i => (X.transpose * Y) i i)) b) =
      ∑ i : ι, inner (𝕜 := ℝ)
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) X (coordinateProjection {i} a))
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Y (coordinateProjection {i} b)) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec_diagonal,
    coordinateProjection_singleton, map_smul, inner_smul_left, inner_smul_right,
    gram_column_inner, starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dyadic_diagonal_gram_bilinear_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2 ^ r))) :
    |inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      (Matrix.diagonal (fun i => (X.transpose * Y) i i)) b)| ≤
      dyadicMatrixSeminorm r a X * dyadicMatrixSeminorm r b Y := by
  rw [diagonal_gram_inner_sum]
  calc
    _ ≤ ∑ i : Fin (2 ^ r), |inner (𝕜 := ℝ)
        (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X (coordinateProjection {i} a))
        (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y (coordinateProjection {i} b))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2 ^ r),
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X (coordinateProjection {i} a)‖ *
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y (coordinateProjection {i} b)‖ :=
      Finset.sum_le_sum fun i _ => abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt (∑ i : Fin (2 ^ r),
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X (coordinateProjection {i} a)‖ ^ 2) *
        Real.sqrt (∑ i : Fin (2 ^ r),
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y (coordinateProjection {i} b)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := mul_le_mul
      (Real.sqrt_le_iff.mpr ⟨apply_nonneg _ _, dyadic_singleton_image_energy_le r X a⟩)
      (Real.sqrt_le_iff.mpr ⟨apply_nonneg _ _, dyadic_singleton_image_energy_le r Y b⟩)
      (Real.sqrt_nonneg _) (apply_nonneg _ _)

theorem dyadic_fullUpper_gram_bilinear_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2 ^ r))) :
    |inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      (fullUpperTruncation (X.transpose * Y)) b)| ≤
      2 * dyadicMatrixSeminorm r a X * dyadicMatrixSeminorm r b Y := by
  rw [fullUpperTruncation_eq, map_add, add_apply, inner_add_right]
  exact (abs_add_le _ _).trans ((add_le_add (dyadic_strict_gram_bilinear_le r X Y a b)
    (dyadic_diagonal_gram_bilinear_le r X Y a b)).trans (by ring_nf; rfl))

theorem dyadic_halfUpper_gram_bilinear_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2 ^ r))) :
    |inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      (halfUpperTruncation (X.transpose * Y)) b)| ≤
      2 * dyadicMatrixSeminorm r a X * dyadicMatrixSeminorm r b Y := by
  have hd := dyadic_diagonal_gram_bilinear_le r X Y a b
  have hp : 0 ≤ dyadicMatrixSeminorm r a X * dyadicMatrixSeminorm r b Y :=
    mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  rw [halfUpperTruncation_eq, half_diagonal_eq_smul, map_add, add_apply,
    inner_add_right, map_smul, smul_apply, inner_smul_right]
  have hh : |(1 / 2 : ℝ) * inner (𝕜 := ℝ) a
      (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
        (Matrix.diagonal (fun i => (X.transpose * Y) i i)) b)| ≤
      dyadicMatrixSeminorm r a X * dyadicMatrixSeminorm r b Y := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith
  exact (abs_add_le _ _).trans ((add_le_add (dyadic_strict_gram_bilinear_le r X Y a b) hh).trans (by ring_nf; rfl))

theorem dyadic_halfUpper_gram_transpose_root_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s : EuclideanSpace ℝ (Fin (2 ^ r))) :
    ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      (halfUpperTruncation (X.transpose * Y)).transpose s‖ ≤
      2 * Real.sqrt (r + 1 : ℕ) * ‖Y‖ * dyadicMatrixSeminorm r s X := by
  generalize hvdef : Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
    (halfUpperTruncation (X.transpose * Y)).transpose s = v
  have h := dyadic_halfUpper_gram_bilinear_le r X Y s v
  rw [← matrix_transpose_inner, hvdef, real_inner_self_eq_norm_sq,
    abs_of_nonneg (sq_nonneg _)] at h
  have hg := dyadicMatrixSeminorm_le r v Y
  have h1 := mul_le_mul_of_nonneg_left hg
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (apply_nonneg (dyadicMatrixSeminorm r s) X))
  have h2 := h.trans h1
  by_cases hvzero : ‖v‖ = 0
  · rw [hvzero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (norm_nonneg _)) (apply_nonneg _ _)
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hvzero)
    apply (mul_le_mul_iff_left₀ hvpos).mp
    convert h2 using 1 <;> ring

end SKConstants
