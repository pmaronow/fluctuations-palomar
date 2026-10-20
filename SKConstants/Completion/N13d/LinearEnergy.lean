module

public import SKConstants.Completion.N13e.Linearization
public import SKConstants.Completion.LM5.ActualCompletion
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open NormedSpace InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13d
open GaussianProposal LC5 LGram N13e LM5

theorem upper_cholesky_weighted_estimate
    (R : ℕ) (ε : ℝ) (EA C H0 EH : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2^R)))
    (hε : 0 ≤ ε) (hsmall : 16*((R+1:ℕ):ℝ)^2*ε ≤ 1)
    (hEA : ‖EA‖ ≤ ε) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0) (hEH : ‖EH‖ ≤ ε) :
    let c := Matrix.toEuclideanCLM (n := Fin (2^R)) (𝕜 := ℝ) C.transpose⁻¹ (s+eq)
    let Q := sevenErrorSum R EA EH s eq b ev
    ‖c-s‖ ≤ 6*Real.sqrt Q ∧
      |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev)-inner (𝕜 := ℝ) s b-
        energyLinearPart EA EH s eq b ev| ≤ 200*((R+1:ℕ):ℝ)*Q := by
  obtain ⟨D,hDu,hDp,hDg,_,_,hcoeff,henergy⟩ :=
    exists_upper_cholesky_with_quadratic_energy_bound R ε EA H0 EH s eq b ev
      hε hsmall hEA hsym hH0 hEH
  have hCD : C = D := upper_cholesky_unique C D hCu hDu hCp hDp (hCg.trans hDg.symm)
  subst D
  exact ⟨hcoeff,henergy⟩

theorem upper_cholesky_weighted_estimate_dim
    (R n : ℕ) (hdim : n=2^R) (ε : ℝ) (EA C H0 EH : Matrix (Fin n) (Fin n) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin n))
    (hε : 0 ≤ ε) (hsmall : 16*((R+1:ℕ):ℝ)^2*ε ≤ 1)
    (hEA : ‖EA‖ ≤ ε) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0) (hEH : ‖EH‖ ≤ ε) :
    let c := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C.transpose⁻¹ (s+eq)
    let Q := sevenErrorSumDim R n hdim EA EH s eq b ev
    ‖c-s‖ ≤ 6*Real.sqrt Q ∧
      |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev)-inner (𝕜 := ℝ) s b-
        energyLinearPart EA EH s eq b ev| ≤ 200*((R+1:ℕ):ℝ)*Q := by
  subst n
  exact upper_cholesky_weighted_estimate R ε EA C H0 EH s eq b ev
    hε hsmall hEA hsym hCu hCp hCg hH0 hEH

theorem padVector_sub {k m : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    padVector m (x-y) = padVector m x-padVector m y := by
  ext i
  obtain ⟨i,rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [padVector]

theorem upper_cholesky_weighted_estimate_padded
    (R k m : ℕ) (hdim : k+m=2^R) (ε : ℝ)
    (EA C H0 EH : Matrix (Fin k) (Fin k) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin k))
    (hε : 0 ≤ ε) (hsmall : 16*((R+1:ℕ):ℝ)^2*ε ≤ 1)
    (hEA : ‖EA‖ ≤ ε) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA) (hCunit : IsUnit C)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0) (hEH : ‖EH‖ ≤ ε) :
    let c := Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) C.transpose⁻¹ (s+eq)
    let Q := sevenErrorSumDim R (k+m) hdim (padMatrix m EA 0) (padMatrix m EH 0)
      (padVector m s) (padVector m eq) (padVector m b) (padVector m ev)
    ‖c-s‖ ≤ 6*Real.sqrt Q ∧
      |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev)-inner (𝕜 := ℝ) s b-
        energyLinearPart EA EH s eq b ev| ≤ 200*((R+1:ℕ):ℝ)*Q := by
  have hgram : (padMatrix m C 1).transpose*padMatrix m C 1 = 1+padMatrix m EA 0 := by
    rw [padMatrix_transpose, padMatrix_mul, hCg]
    simpa only [one_mul, add_zero, padMatrix_add, padMatrix_one]
      using (padMatrix_add (m := m) 1 EA 1 0)
  have hCt : IsUnit C.transpose := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp hCunit
  have h := upper_cholesky_weighted_estimate_dim R (k+m) hdim ε
    (padMatrix m EA 0) (padMatrix m C 1) (padMatrix m H0 0) (padMatrix m EH 0)
    (padVector m s) (padVector m eq) (padVector m b) (padVector m ev)
    hε hsmall (by rwa [padMatrix_norm]) (by rw [padMatrix_transpose,hsym])
    (padMatrix_upper C hCu) (padMatrix_positive C hCp) hgram
    (padMatrix_strictLower H0 hH0) (by rwa [padMatrix_norm])
  simpa only [← padMatrix_add, zero_add, ← padVector_add, padMatrix_transpose,
    padMatrix_inv _ hCt, padMatrix_apply, ← padVector_sub, padVector_norm,
    query_energy_padding C (H0+EH) hCunit, padVector_inner,
    energyLinearPart_padding] using h

theorem projectedQueryEnergy_weighted_estimate_padded
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R k m : ℕ) (hdim : k+m=2^R) (ε : ℝ) (T g : Fin k → E) (x : E)
    (s b : EuclideanSpace ℝ (Fin k)) (H0 : Matrix (Fin k) (Fin k) ℝ)
    (hε : 0 ≤ ε) (hsmall : 16*((R+1:ℕ):ℝ)^2*ε ≤ 1)
    (hEA : ‖familyGram T-1‖ ≤ ε)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0) (hEH : ‖familyCross T g-H0‖ ≤ ε) :
    let Q := sevenErrorSumDim R (k+m) hdim
      (padMatrix m (familyGram T-1) 0) (padMatrix m (familyCross T g-H0) 0)
      (padVector m s) (padVector m (familyCoordinates T x-s))
      (padVector m b) (padVector m (familyCoordinates g x-b))
    ‖familyCoordinates (gramSchmidtNormed ℝ T) x-s‖ ≤ 6*Real.sqrt Q ∧
      |projectedQueryEnergy (gramSchmidtNormed ℝ T) g x-inner (𝕜 := ℝ) s b-
        energyLinearPart (familyGram T-1) (familyCross T g-H0)
          s (familyCoordinates T x-s) b (familyCoordinates g x-b)| ≤
        200*((R+1:ℕ):ℝ)*Q := by
  have hd : 1 ≤ ((R+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hGram : ‖familyGram T-1‖ ≤ (3/4:ℝ) := hEA.trans (by
    have hm := mul_le_mul_of_nonneg_right
      (show (1:ℝ) ≤ ((R+1:ℕ):ℝ)^2 by nlinarith) hε
    nlinarith)
  have hsym : (familyGram T-1).transpose = familyGram T-1 := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, familyGram, Matrix.one_apply]
    rw [real_inner_comm]
    split_ifs <;> simp_all
  have hg : (gramSchmidtCholesky T).transpose*gramSchmidtCholesky T =
      1+(familyGram T-1) := by rw [gramSchmidtCholesky_gram T hGram]; abel
  have h := upper_cholesky_weighted_estimate_padded R k m hdim ε (familyGram T-1)
    (gramSchmidtCholesky T) H0 (familyCross T g-H0) s (familyCoordinates T x-s)
    b (familyCoordinates g x-b) hε hsmall hEA hsym (gramSchmidtCholesky_upper T)
    (gramSchmidtCholesky_positive T hGram) hg (gramSchmidtCholesky_isUnit T hGram) hH0 hEH
  rw [projectedQueryEnergy_eq_cholesky T g hGram x,
    gramSchmidt_coordinates T hGram x]
  simpa only [add_sub_cancel] using h

end SKConstants.Completion.N13d
