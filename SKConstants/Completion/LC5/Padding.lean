module

public import SKConstants.Completion.LC5.OperatorEnergy
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LC5

def padMatrix {k : ℕ} (m : ℕ) (A : Matrix (Fin k) (Fin k) ℝ) (a : ℝ) :
    Matrix (Fin (k+m)) (Fin (k+m)) ℝ :=
  (Matrix.fromBlocks A 0 0 (a • (1 : Matrix (Fin m) (Fin m) ℝ))).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm

def padVector {k : ℕ} (m : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin (k+m)) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun _ : Fin m => (0 : ℝ)) ∘ finSumFinEquiv.symm)

theorem padMatrix_add {k m : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (a b : ℝ) :
    padMatrix m (A+B) (a+b) = padMatrix m A a + padMatrix m B b := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [padMatrix, add_smul]

theorem padMatrix_one {k m : ℕ} : padMatrix m (1 : Matrix (Fin k) (Fin k) ℝ) 1 = 1 := by
  simp [padMatrix, Matrix.fromBlocks_one]

theorem padVector_add {k m : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    padVector m (x+y) = padVector m x + padVector m y := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [padVector]

@[simp] theorem padMatrix_first {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (a : ℝ) (i j : Fin k) : padMatrix m A a (i.castAdd m) (j.castAdd m) = A i j := by
  simp [padMatrix, finSumFinEquiv]

@[simp] theorem padVector_first {k m : ℕ} (x : EuclideanSpace ℝ (Fin k))
    (i : Fin k) : padVector m x (i.castAdd m) = x i := by
  simp [padVector, finSumFinEquiv]

theorem padMatrix_mul {k m : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (a b : ℝ) :
    padMatrix m A a * padMatrix m B b = padMatrix m (A*B) (a*b) := by
  unfold padMatrix
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  simp [Matrix.fromBlocks_multiply, Matrix.mul_smul, smul_smul, mul_comm]

@[simp] theorem padMatrix_transpose {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (a : ℝ) :
    (padMatrix m A a).transpose = padMatrix m A.transpose a := by
  unfold padMatrix
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]

theorem padMatrix_inv {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsUnit A) :
    (padMatrix m A 1)⁻¹ = padMatrix m A⁻¹ 1 := by
  unfold padMatrix
  rw [Matrix.inv_submatrix_equiv]
  simp only [one_smul]
  rw [Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff A 0 1 (by simp [hA])]
  simp

theorem padMatrix_fullUpper {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    fullUpperTruncation (padMatrix m A 0) = padMatrix m (fullUpperTruncation A) 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [padMatrix, fullUpperTruncation, finSumFinEquiv]
  congr 1

theorem padMatrix_halfUpper {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    halfUpperTruncation (padMatrix m A 0) = padMatrix m (halfUpperTruncation A) 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;> simp [padMatrix, halfUpperTruncation, finSumFinEquiv]
  congr 1

theorem padVector_inner {k m : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    inner (𝕜 := ℝ) (padVector m x) (padVector m y) = inner (𝕜 := ℝ) x y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  rw [← finSumFinEquiv.sum_comp]
  simp [padVector, Function.comp_def]

theorem padVector_norm {k m : ℕ} (x : EuclideanSpace ℝ (Fin k)) : ‖padVector m x‖ = ‖x‖ := by
  have h := padVector_inner (m := m) x x
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (padVector m x), norm_nonneg x]

theorem padMatrix_apply {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    Matrix.toEuclideanCLM (n := Fin (k+m)) (𝕜 := ℝ) (padMatrix m A a) (padVector m x) =
      padVector m (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A x) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  change ((padMatrix m A a) *ᵥ (padVector m x)) _ = _
  unfold Matrix.mulVec dotProduct
  rw [← finSumFinEquiv.sum_comp]
  cases i <;> simp [padMatrix, padVector, Function.comp_def, Matrix.mulVec, dotProduct]

def firstVector {k m : ℕ} (x : EuclideanSpace ℝ (Fin (k+m))) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => x (i.castAdd m))

theorem firstVector_norm_le {k m : ℕ} (x : EuclideanSpace ℝ (Fin (k+m))) :
    ‖firstVector x‖ ≤ ‖x‖ := by
  have he : ‖x‖^2 = ‖firstVector x‖^2 + ∑ i : Fin m, (x (i.natAdd k))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    rw [← finSumFinEquiv.sum_comp]
    simp [firstVector, finSumFinEquiv]
  have hp : 0 ≤ ∑ i : Fin m, (x (i.natAdd k))^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [norm_nonneg (firstVector x), norm_nonneg x]

theorem padMatrix_apply_general {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin (k+m))) :
    Matrix.toEuclideanCLM (n := Fin (k+m)) (𝕜 := ℝ) (padMatrix m A 0) x =
      padVector m (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A (firstVector x)) := by
  ext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  change ((padMatrix m A 0) *ᵥ x) _ = _
  unfold Matrix.mulVec dotProduct
  rw [← finSumFinEquiv.sum_comp]
  cases i <;> simp [padMatrix, padVector, firstVector, finSumFinEquiv, Matrix.mulVec, dotProduct]

theorem padMatrix_norm {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    ‖padMatrix m A 0‖ = ‖A‖ := by
  apply le_antisymm
  · change ‖Matrix.toEuclideanCLM (n := Fin (k+m)) (𝕜 := ℝ) (padMatrix m A 0)‖ ≤ ‖A‖
    apply (Matrix.toEuclideanCLM (n := Fin (k+m)) (𝕜 := ℝ) (padMatrix m A 0)).opNorm_le_bound
      (norm_nonneg A)
    intro x
    rw [padMatrix_apply_general, padVector_norm]
    calc
      _ ≤ ‖A‖ * ‖firstVector (k := k) (m := m) x‖ := by
        simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
          (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A).le_opNorm
            (firstVector (k := k) (m := m) x)
      _ ≤ _ := mul_le_mul_of_nonneg_left (firstVector_norm_le (k := k) (m := m) x) (norm_nonneg A)
  · change ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A‖ ≤ ‖padMatrix m A 0‖
    apply (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A).opNorm_le_bound
      (norm_nonneg (padMatrix m A 0))
    intro x
    have h := (Matrix.toEuclideanCLM (n := Fin (k+m)) (𝕜 := ℝ) (padMatrix m A 0)).le_opNorm
      (padVector m x)
    simpa only [padMatrix_apply, padVector_norm, Matrix.l2_opNorm_toEuclideanCLM] using h

theorem padMatrix_upper {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, j < i → A i j = 0) :
    ∀ i j, j < i → padMatrix m A 1 i j = 0 := by
  intro i j hji
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [padMatrix] using hA i j hji
    | inr j => simp [padMatrix]
  | inr i =>
    cases j with
    | inl j => simp [padMatrix]
    | inr j =>
      have hne : i ≠ j := by
        intro he
        subst j
        exact (lt_irrefl _) hji
      simp [padMatrix, Matrix.one_apply_ne hne]

theorem padMatrix_positive {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i, 0 < A i i) : ∀ i, 0 < padMatrix m A 1 i i := by
  intro i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [padMatrix, hA]

theorem padMatrix_strictLower {k m : ℕ} (H : Matrix (Fin k) (Fin k) ℝ)
    (hH : ∀ i j, i ≤ j → H i j = 0) :
    ∀ i j, i ≤ j → padMatrix m H 0 i j = 0 := by
  intro i j hij
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa [padMatrix] using hH i j hij
    | inr j => simp [padMatrix]
  | inr i => cases j <;> simp [padMatrix]

theorem query_energy_padding {k m : ℕ} (C H : Matrix (Fin k) (Fin k) ℝ)
    (hC : IsUnit C) (q v : EuclideanSpace ℝ (Fin k)) :
    queryEnergyNormalForm (padMatrix m C 1) (padMatrix m H 0)
      (padVector m q) (padVector m v) = queryEnergyNormalForm C H q v := by
  have hCt : IsUnit C.transpose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp hC
  simp only [queryEnergyNormalForm, padMatrix_transpose, padMatrix_inv _ hCt,
    padMatrix_mul, mul_zero, padMatrix_fullUpper, padMatrix_apply, padVector_inner]

theorem upper_cholesky_energy_of_operator_errors_dim
    (R n : ℕ) (hdim : n = 2^R) (η : ℝ)
    (EA C H0 EH : Matrix (Fin n) (Fin n) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin n))
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖EA‖ ≤ η) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖EH‖ ≤ η) (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b| ≤
      queryError R η := by
  subst n
  exact upper_cholesky_energy_of_operator_errors R η EA C H0 EH s eq b ev
    hη hsmall hEA hsym hCu hCp hCg hH0 hEH heq hev hs hb

theorem upper_cholesky_energy_of_operator_errors_padded
    (R k m : ℕ) (hdim : k+m = 2^R) (η : ℝ)
    (EA C H0 EH : Matrix (Fin k) (Fin k) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin k))
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖EA‖ ≤ η) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA) (hC : IsUnit C)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖EH‖ ≤ η) (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b| ≤
      queryError R η := by
  have hsym' : (padMatrix m EA 0).transpose = padMatrix m EA 0 := by
    rw [padMatrix_transpose, hsym]
  have hgram' : (padMatrix m C 1).transpose * padMatrix m C 1 = 1+padMatrix m EA 0 := by
    rw [padMatrix_transpose, padMatrix_mul, one_mul, hCg]
    simpa only [padMatrix_one, add_zero] using padMatrix_add (m := m) 1 EA 1 0
  have h := upper_cholesky_energy_of_operator_errors_dim R (k+m) hdim η
    (padMatrix m EA 0) (padMatrix m C 1) (padMatrix m H0 0) (padMatrix m EH 0)
    (padVector m s) (padVector m eq) (padVector m b) (padVector m ev)
    hη hsmall (by rwa [padMatrix_norm]) hsym' (padMatrix_upper C hCu)
    (padMatrix_positive C hCp) hgram' (padMatrix_strictLower H0 hH0)
    (by rwa [padMatrix_norm]) (by rwa [padVector_norm]) (by rwa [padVector_norm])
    (by rwa [padVector_norm]) (by rwa [padVector_norm])
  rw [← padVector_add, ← padVector_add, ← padMatrix_add, zero_add,
    query_energy_padding C (H0+EH) hC, padVector_inner] at h
  exact h

end SKConstants.Completion.LC5
