module

public import SKConstants.DyadicCover
public import SKConstants.CholeskyBarrier
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

@[expose] def coordinateProjection (I : Finset ι) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι := WithLp.toLp ((2 : ℕ) : ENNReal) fun i => if i ∈ I then x i else 0

omit [Fintype ι] in
@[simp] theorem coordinateProjection_apply (I : Finset ι) (x : EuclideanSpace ℝ ι)
    (i : ι) : coordinateProjection I x i = if i ∈ I then x i else 0 := rfl

theorem coordinateProjection_norm_sq (I : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖coordinateProjection I x‖ ^ 2 = ∑ i ∈ I, (x i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [coordinateProjection_apply, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  simp

theorem coordinateProjection_norm_le (I : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖coordinateProjection I x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [coordinateProjection_norm_sq, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
    (fun i _ _ => sq_nonneg (x i))

omit [Fintype ι] in
theorem coordinateProjection_eq_sum (I : Finset ι) (x : EuclideanSpace ℝ ι) :
    coordinateProjection I x = ∑ i ∈ I, x i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  simp [coordinateProjection, Pi.single_apply]

omit [Fintype ι] in
theorem coordinateProjection_singleton (i : ι) (x : EuclideanSpace ℝ ι) :
    coordinateProjection {i} x = x i • EuclideanSpace.single i (1 : ℝ) := by
  rw [coordinateProjection_eq_sum]
  simp

theorem matrix_projected_column_sum (A : Matrix ι ι ℝ)
    (I : Finset ι) (x : EuclideanSpace ℝ ι) :
    (∑ i ∈ I, x i • Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
      (EuclideanSpace.single i (1 : ℝ))) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (coordinateProjection I x) := by
  rw [coordinateProjection_eq_sum]
  simp

theorem matrix_entry_abs_le_opNorm (A : Matrix ι ι ℝ) (i j : ι) :
    |A i j| ≤ ‖A‖ := by
  have hcoord := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
    (EuclideanSpace.single j (1 : ℝ))) i
  have hop := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm
    (EuclideanSpace.single j (1 : ℝ))
  have heval : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
      (EuclideanSpace.single j (1 : ℝ))) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  rw [heval, Real.norm_eq_abs] at hcoord
  exact hcoord.trans (by simpa only [PiLp.norm_single, norm_one, mul_one,
    Matrix.l2_opNorm_toEuclideanCLM] using hop)

theorem matrix_column_apply (A : Matrix ι ι ℝ) (i j : ι) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
      (EuclideanSpace.single j (1 : ℝ))) i = A i j := by
  change (A *ᵥ Pi.single j 1) i = A i j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']

theorem matrix_transpose_opNorm (A : Matrix ι ι ℝ) : ‖A.transpose‖ = ‖A‖ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose A

theorem gramMatrix_action_norm_le (X Y : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (X.transpose * Y) w‖ ≤
      ‖X‖ * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Y w‖ := by
  rw [map_mul, mul_apply_eq_comp]
  have h := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) X.transpose).le_opNorm
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Y w)
  simpa only [Matrix.l2_opNorm_toEuclideanCLM, matrix_transpose_opNorm] using h

theorem gram_column_inner (X Y : Matrix ι ι ℝ) (i j : ι) :
    inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) X (EuclideanSpace.single i (1 : ℝ)))
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Y (EuclideanSpace.single j (1 : ℝ))) =
      (X.transpose * Y) i j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial, matrix_column_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem matrix_transpose_inner (A : Matrix ι ι ℝ) (x y : EuclideanSpace ℝ ι) :
    inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A.transpose x) y =
      inner (𝕜 := ℝ) x (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A y) := by
  rw [real_inner_comm y (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A.transpose x),
    Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

section Ordered

variable [LinearOrder ι]

@[expose] def strictUpperTruncation (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if i < j then A i j else 0

theorem strictUpperTruncation_inner_eq (A : Matrix ι ι ℝ)
    (a b : EuclideanSpace ℝ ι) :
    inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (strictUpperTruncation A) b) =
      ∑ p ∈ (Finset.univ.filter fun p : ι × ι => p.1 < p.2),
        inner (𝕜 := ℝ) (a p.1 • EuclideanSpace.single p.1 (1 : ℝ))
          (b p.2 • Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
            (EuclideanSpace.single p.2 (1 : ℝ))) := by
  rw [Matrix.inner_toEuclideanCLM]
  simp only [Finset.sum_filter, Fintype.sum_prod_type, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_single_left, map_one, one_mul, matrix_column_apply]
  simp only [dotProduct, Matrix.mulVec, strictUpperTruncation, ite_mul, zero_mul,
    Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [starRingEnd_apply, star_trivial]
  all_goals ring

end Ordered

theorem projection_energy_eq_incidence (sets : ρ → Finset ι)
    (x : EuclideanSpace ℝ ι) :
    ∑ u : ρ, ‖coordinateProjection (sets u) x‖ ^ 2 =
      ∑ i : ι, (∑ u : ρ, if i ∈ sets u then (1 : ℝ) else 0) * (x i) ^ 2 := by
  simp only [coordinateProjection_norm_sq]
  have hf (u : ρ) : (∑ i ∈ sets u, (x i) ^ 2) =
      ∑ i : ι, if i ∈ sets u then (x i) ^ 2 else 0 := by simp
  simp_rw [hf]
  rw [Finset.sum_comm]
  congr 1
  ext i
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem projection_energy_le_of_incidence (sets : ρ → Finset ι)
    (x : EuclideanSpace ℝ ι) (d : ℝ)
    (hcount : ∀ i, (∑ u : ρ, if i ∈ sets u then (1 : ℝ) else 0) ≤ d) :
    ∑ u : ρ, ‖coordinateProjection (sets u) x‖ ^ 2 ≤ d * ‖x‖ ^ 2 := by
  rw [projection_energy_eq_incidence, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcount i) (sq_nonneg _)

theorem matrix_projection_energy_le (A : Matrix ι ι ℝ) (sets : ρ → Finset ι)
    (x : EuclideanSpace ℝ ι) (d : ℝ)
    (hcount : ∀ i, (∑ u : ρ, if i ∈ sets u then (1 : ℝ) else 0) ≤ d) :
    ∑ u : ρ, ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
      (coordinateProjection (sets u) x)‖ ^ 2 ≤ ‖A‖ ^ 2 * (d * ‖x‖ ^ 2) := by
  calc
    _ ≤ ∑ u : ρ, ‖A‖ ^ 2 * ‖coordinateProjection (sets u) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro u _
      have hop := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A).le_opNorm
        (coordinateProjection (sets u) x)
      rw [Matrix.l2_opNorm_toEuclideanCLM] at hop
      have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hop
      simpa only [mul_pow] using hs
    _ = ‖A‖ ^ 2 * (∑ u : ρ, ‖coordinateProjection (sets u) x‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (projection_energy_le_of_incidence sets x d hcount)
      (sq_nonneg _)

@[expose] def projectedMatrixFeatureMap (sets : ρ → Finset ι)
    (w : EuclideanSpace ℝ ι) : Matrix ι ι ℝ →ₗ[ℝ] EuclideanSpace ℝ (ρ × ι) where
  toFun A := WithLp.toLp ((2 : ℕ) : ENNReal) fun p =>
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A (coordinateProjection (sets p.1) w) p.2
  map_add' A B := by
    ext p
    simp [map_add]
  map_smul' a A := by
    ext p
    simp [map_smul]

@[expose] def projectedMatrixSeminorm (sets : ρ → Finset ι)
    (w : EuclideanSpace ℝ ι) : Seminorm ℝ (Matrix ι ι ℝ) :=
  (normSeminorm ℝ (EuclideanSpace ℝ (ρ × ι))).comp (projectedMatrixFeatureMap sets w)

theorem projectedMatrixSeminorm_sq (sets : ρ → Finset ι) (w : EuclideanSpace ℝ ι)
    (A : Matrix ι ι ℝ) :
    projectedMatrixSeminorm sets w A ^ 2 =
      ∑ u : ρ, ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
        (coordinateProjection (sets u) w)‖ ^ 2 := by
  change ‖projectedMatrixFeatureMap sets w A‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem projectedMatrixSeminorm_le (sets : ρ → Finset ι) (w : EuclideanSpace ℝ ι)
    (A : Matrix ι ι ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hcount : ∀ i, (∑ u : ρ, if i ∈ sets u then (1 : ℝ) else 0) ≤ d) :
    projectedMatrixSeminorm sets w A ≤ Real.sqrt d * ‖A‖ * ‖w‖ := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp
  rw [projectedMatrixSeminorm_sq]
  have h := matrix_projection_energy_le A sets w d hcount
  convert h using 1
  simp only [mul_pow, Real.sq_sqrt hd]
  ring

namespace DyadicCore

theorem left_incidence_le (r : ℕ) (i : Fin (leafCount r)) :
    (∑ node : Node r, if i ∈ left r node then (1 : ℝ) else 0) ≤ r := by
  induction r with
  | zero => simp [Node]
  | succ r ih =>
      cases i using Fin.addCases with
      | left i =>
          change (∑ node : Unit ⊕ (Node r ⊕ Node r),
            if Fin.castAdd _ i ∈ left (r+1) node then (1 : ℝ) else 0) ≤ (r+1 : ℕ)
          simp only [Fintype.sum_sum_type, left, castAdd_mem_castAdd,
            castAdd_not_mem_natAdd, Finset.mem_univ, ite_true, ite_false,
            Finset.sum_const_zero, Fintype.sum_unique, add_zero,
            Nat.cast_add, Nat.cast_one]
          linarith [ih i]
      | right i =>
          change (∑ node : Unit ⊕ (Node r ⊕ Node r),
            if Fin.natAdd _ i ∈ left (r+1) node then (1 : ℝ) else 0) ≤ (r+1 : ℕ)
          simp only [Fintype.sum_sum_type, left, natAdd_not_mem_castAdd,
            natAdd_mem_natAdd, ite_false, Finset.sum_const_zero, zero_add]
          exact (ih i).trans (by norm_cast; omega)

theorem right_incidence_le (r : ℕ) (i : Fin (leafCount r)) :
    (∑ node : Node r, if i ∈ right r node then (1 : ℝ) else 0) ≤ r := by
  induction r with
  | zero => simp [Node]
  | succ r ih =>
      cases i using Fin.addCases with
      | left i =>
          change (∑ node : Unit ⊕ (Node r ⊕ Node r),
            if Fin.castAdd _ i ∈ right (r+1) node then (1 : ℝ) else 0) ≤ (r+1 : ℕ)
          simp only [Fintype.sum_sum_type, right, castAdd_not_mem_natAdd,
            castAdd_mem_castAdd, ite_false, Finset.sum_const_zero, add_zero, zero_add]
          exact (ih i).trans (by norm_cast; omega)
      | right i =>
          change (∑ node : Unit ⊕ (Node r ⊕ Node r),
            if Fin.natAdd _ i ∈ right (r+1) node then (1 : ℝ) else 0) ≤ (r+1 : ℕ)
          simp only [Fintype.sum_sum_type, right, natAdd_mem_natAdd,
            natAdd_not_mem_castAdd, Finset.mem_univ, ite_true, ite_false,
            Finset.sum_const_zero, Fintype.sum_unique, zero_add,
            Nat.cast_add, Nat.cast_one]
          linarith [ih i]

end DyadicCore

theorem dyadicLeft_incidence_le (r : ℕ) (i : Fin (2 ^ r)) :
    (∑ node : DyadicCore.Node r, if i ∈ dyadicLeft r node then (1 : ℝ) else 0) ≤ r := by
  let e := Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)
  convert DyadicCore.left_incidence_le r (e.symm i) using 1
  apply Finset.sum_congr rfl
  intro node _
  simp only [dyadicLeft, Finset.mem_map_equiv]
  rfl

theorem dyadicRight_incidence_le (r : ℕ) (i : Fin (2 ^ r)) :
    (∑ node : DyadicCore.Node r, if i ∈ dyadicRight r node then (1 : ℝ) else 0) ≤ r := by
  let e := Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)
  convert DyadicCore.right_incidence_le r (e.symm i) using 1
  apply Finset.sum_congr rfl
  intro node _
  simp only [dyadicRight, Finset.mem_map_equiv]
  rfl

theorem strictUpperTruncation_bilinear_le (r : ℕ) (A : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (a b : EuclideanSpace ℝ (Fin (2 ^ r))) :
    |inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      (strictUpperTruncation A) b)| ≤ r * ‖A‖ * ‖a‖ * ‖b‖ := by
  have h := dyadic_rectangle_bound r
    (fun i => EuclideanSpace.single i (1 : ℝ))
    (fun j => Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) A
      (EuclideanSpace.single j (1 : ℝ))) a b
  rw [← strictUpperTruncation_inner_eq] at h
  simp_rw [← coordinateProjection_eq_sum, matrix_projected_column_sum] at h
  have hleft := projection_energy_le_of_incidence (dyadicLeft r) a (r : ℝ)
    (dyadicLeft_incidence_le r)
  have hright := matrix_projection_energy_le A (dyadicRight r) b (r : ℝ)
    (dyadicRight_incidence_le r)
  have hsqrtleft : Real.sqrt (∑ node : DyadicCore.Node r,
      ‖coordinateProjection (dyadicLeft r node) a‖ ^ 2) ≤ Real.sqrt r * ‖a‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)] using hleft
  have hsqrtright : Real.sqrt (∑ node : DyadicCore.Node r,
      ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) A
        (coordinateProjection (dyadicRight r node) b)‖ ^ 2) ≤
        ‖A‖ * (Real.sqrt r * ‖b‖) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)] using hright
  calc
    _ ≤ _ := h
    _ ≤ (Real.sqrt r * ‖a‖) * (‖A‖ * (Real.sqrt r * ‖b‖)) :=
      mul_le_mul hsqrtleft hsqrtright (Real.sqrt_nonneg _) (by positivity)
    _ = r * ‖A‖ * ‖a‖ * ‖b‖ := by
      calc
        _ = (Real.sqrt r) ^ 2 * ‖A‖ * ‖a‖ * ‖b‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg r)]

theorem strictUpperTruncation_opNorm_le (r : ℕ)
    (A : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :
    ‖strictUpperTruncation A‖ ≤ r * ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
  intro x y hx hy
  have h := strictUpperTruncation_bilinear_le r A y x
  rw [hx, hy, mul_one, mul_one] at h
  have heq : RCLike.re (inner (𝕜 := ℝ)
      (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (strictUpperTruncation A) x) y) =
      inner (𝕜 := ℝ) y
        (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (strictUpperTruncation A) x) := by
    simp [real_inner_comm]
  rw [heq]
  exact (le_abs_self _).trans h

theorem diagonal_opNorm_le (A : Matrix ι ι ℝ) :
    ‖Matrix.diagonal (fun i => A i i)‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using matrix_entry_abs_le_opNorm A i i

theorem half_diagonal_opNorm_le (A : Matrix ι ι ℝ) :
    ‖Matrix.diagonal (fun i => A i i / 2)‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := matrix_entry_abs_le_opNorm A i i
  have hn := norm_nonneg A
  linarith

omit [Fintype ι] in
theorem half_diagonal_eq_smul (A : Matrix ι ι ℝ) :
    Matrix.diagonal (fun i => A i i / 2) = (1 / 2 : ℝ) • Matrix.diagonal (fun i => A i i) := by
  ext i j
  by_cases h : i = j <;> simp [h, smul_eq_mul]
  all_goals ring

@[expose] def fullUpperTruncation [LinearOrder ι] (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => if i ≤ j then A i j else 0

omit [Fintype ι] in
theorem fullUpperTruncation_eq [LinearOrder ι] (A : Matrix ι ι ℝ) :
    fullUpperTruncation A = strictUpperTruncation A + Matrix.diagonal (fun i => A i i) := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [fullUpperTruncation, strictUpperTruncation, hij, hij.le, ne_of_lt hij]
  · subst j
    simp [fullUpperTruncation, strictUpperTruncation]
  · simp [fullUpperTruncation, strictUpperTruncation, not_le_of_gt hij,
      not_lt_of_gt hij, ne_of_gt hij]

omit [Fintype ι] in
theorem halfUpperTruncation_eq [LinearOrder ι] (A : Matrix ι ι ℝ) :
    halfUpperTruncation A = strictUpperTruncation A + Matrix.diagonal (fun i => A i i / 2) := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [halfUpperTruncation, strictUpperTruncation, hij, ne_of_lt hij]
  · subst j
    simp [halfUpperTruncation, strictUpperTruncation]
  · simp [halfUpperTruncation, strictUpperTruncation,
      not_lt_of_gt hij, ne_of_gt hij]

theorem fullUpperTruncation_opNorm_le (r : ℕ)
    (A : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :
    ‖fullUpperTruncation A‖ ≤ (r + 1 : ℕ) * ‖A‖ := by
  rw [fullUpperTruncation_eq]
  calc
    _ ≤ ‖strictUpperTruncation A‖ + ‖Matrix.diagonal (fun i => A i i)‖ := norm_add_le _ _
    _ ≤ r * ‖A‖ + ‖A‖ := add_le_add (strictUpperTruncation_opNorm_le r A) (diagonal_opNorm_le A)
    _ = _ := by push_cast; ring

theorem halfUpperTruncation_opNorm_le (r : ℕ)
    (A : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :
    ‖halfUpperTruncation A‖ ≤ (r + 1 : ℕ) * ‖A‖ := by
  rw [halfUpperTruncation_eq]
  calc
    _ ≤ ‖strictUpperTruncation A‖ + ‖Matrix.diagonal (fun i => A i i / 2)‖ := norm_add_le _ _
    _ ≤ r * ‖A‖ + ‖A‖ := add_le_add (strictUpperTruncation_opNorm_le r A) (half_diagonal_opNorm_le A)
    _ = _ := by push_cast; ring

@[expose] def halfUpperLinearMap [LinearOrder ι] : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ where
  toFun := halfUpperTruncation
  map_add' A B := by
    ext i j
    simp only [halfUpperTruncation, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' a A := by
    ext i j
    simp only [halfUpperTruncation, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

@[expose] def halfUpperCLM (r : ℕ) :
    Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ →L[ℝ]
      Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ :=
  halfUpperLinearMap.mkContinuous (r + 1 : ℕ) (halfUpperTruncation_opNorm_le r)

@[simp] theorem halfUpperCLM_apply (r : ℕ)
    (A : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :
    halfUpperCLM r A = halfUpperTruncation A := rfl

end SKConstants
