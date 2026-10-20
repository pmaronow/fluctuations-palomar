module

public import SKConstants.GaussianProposalOrthogonalInvariant
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

@[expose] def quadraticEnergy (N : ℝ) (x : ι → ℝ) (W : Matrix ι ι ℝ) : ℝ :=
  (1 / 2 : ℝ) * N⁻¹ * (x ⬝ᵥ W *ᵥ x)

@[expose] def quadraticEnergyLM (N : ℝ) (x : ι → ℝ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun := quadraticEnergy N x
  map_add' := by
    intro A B
    simp only [quadraticEnergy, Matrix.add_mulVec, dotProduct_add]
    ring
  map_smul' := by
    intro a A
    simp only [quadraticEnergy, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      RingHom.id_apply]
    ring

theorem quadraticEnergy_rankOne (N : ℝ) (x u v : ι → ℝ) :
    quadraticEnergy N x (Matrix.vecMulVec u v) =
      (1 / 2 : ℝ) * N⁻¹ * (x ⬝ᵥ u) * (x ⬝ᵥ v) := by
  unfold quadraticEnergy
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct,
    dotProduct_comm v x]
  simp only [smul_eq_mul]
  ring

@[expose] def columnAssembly (N : ℝ) (u f : κ → ι → ℝ) (d : κ → ℝ)
    (R : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (∑ k, N⁻¹ • (Matrix.vecMulVec (u k) (f k) + Matrix.vecMulVec (f k) (u k))) +
    (∑ k, (N⁻¹ * d k) • Matrix.vecMulVec (u k) (u k)) + R

theorem columnAssembly_energy (N : ℝ) (x : ι → ℝ) (u f : κ → ι → ℝ)
    (d : κ → ℝ) (R : Matrix ι ι ℝ) :
    quadraticEnergy N x (columnAssembly N u f d R) =
      (∑ k, (N⁻¹ * (x ⬝ᵥ u k)) * (N⁻¹ * (x ⬝ᵥ f k))) +
        (1 / 2 : ℝ) * (∑ k, (N⁻¹ * (x ⬝ᵥ u k)) ^ 2 * d k) +
        quadraticEnergy N x R := by
  change quadraticEnergyLM N x (columnAssembly N u f d R) = _
  unfold columnAssembly
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  change
    (∑ k, N⁻¹ * (quadraticEnergy N x (Matrix.vecMulVec (u k) (f k)) +
      quadraticEnergy N x (Matrix.vecMulVec (f k) (u k)))) +
    (∑ k, (N⁻¹ * d k) * quadraticEnergy N x (Matrix.vecMulVec (u k) (u k))) +
      quadraticEnergy N x R = _
  simp only [quadraticEnergy_rankOne]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem quadraticEnergy_projected (N : ℝ) (x : ι → ℝ)
    (P W : Matrix ι ι ℝ) (hP : P.IsSymm) :
    quadraticEnergy N x (P * W * P) = quadraticEnergy N (P *ᵥ x) W := by
  have hvec : x ᵥ* P = P *ᵥ x := by
    calc
      x ᵥ* P = x ᵥ* Pᵀ := by rw [hP]
      _ = P *ᵥ x := Matrix.vecMul_transpose P x
  unfold quadraticEnergy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, hvec]

theorem quadraticEnergy_goe (N sigma : ℝ) (x : ι → ℝ)
    (z : EuclideanSpace ℝ (ι × ι)) :
    quadraticEnergy N x (goeMatrix sigma z) =
      (1 / 2 : ℝ) * N⁻¹ * goeBilinear sigma x x z := by
  unfold quadraticEnergy
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm, ← goeBilinear_eq_matrix]

theorem residualGOE_energy_mean (N sigma : ℝ) (x : ι → ℝ) :
    (∫ z, quadraticEnergy N x (goeMatrix sigma z) ∂primitiveGaussian (ι × ι)) = 0 := by
  simp_rw [quadraticEnergy_goe]
  rw [integral_const_mul, goeBilinear_mean]
  simp

theorem residualGOE_energy_variance (N sigma : ℝ) (x : ι → ℝ) :
    Var[fun z => quadraticEnergy N x (goeMatrix sigma z); primitiveGaussian (ι × ι)] =
      N⁻¹ ^ 2 * sigma ^ 2 * (dot x x) ^ 2 := by
  have hfun : (fun z => quadraticEnergy N x (goeMatrix sigma z)) =
      fun z => ((1 / 2 : ℝ) * N⁻¹) * goeBilinear sigma x x z := by
    funext z
    exact quadraticEnergy_goe N sigma x z
  rw [hfun, variance_const_mul,
    ← covariance_self (goeBilinear_gaussian sigma x x).aemeasurable,
    goeBilinear_covariance]
  ring

@[expose] def discardedDiagonalEnergy (delta : ℝ) (c : κ → ℝ)
    (z : EuclideanSpace ℝ κ) : ℝ :=
  linearForm (fun k => (1 / 2 : ℝ) * delta * c k ^ 2) z

theorem discardedDiagonal_energy_mean (delta : ℝ) (c : κ → ℝ) :
    (∫ z, discardedDiagonalEnergy delta c z ∂primitiveGaussian κ) = 0 := by
  exact linearForm_mean _

theorem discardedDiagonal_energy_variance (delta : ℝ) (c : κ → ℝ) :
    Var[discardedDiagonalEnergy delta c; primitiveGaussian κ] =
      (delta ^ 2 / 4) * ∑ k, c k ^ 4 := by
  unfold discardedDiagonalEnergy
  rw [← covariance_self (linearForm_gaussian _).aemeasurable, linearForm_covariance,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end SKConstants.GaussianProposal
