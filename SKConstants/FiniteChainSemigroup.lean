module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Analysis.SpecialFunctions.Exponential

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Operator

namespace SKConstants

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The generator of a finite chain with a rate-one Poisson update clock. -/
@[expose] def finiteChainGenerator (K : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ := K - 1

/-- The actual continuous-time transition matrix with generator `K - I`. -/
@[expose] def finiteChainSemigroup (K : Matrix Ω Ω ℝ) (t : ℝ) : Matrix Ω Ω ℝ :=
  NormedSpace.exp (t • finiteChainGenerator K)

theorem matrix_exp_smul_one (t : ℝ) :
    NormedSpace.exp (t • (1 : Matrix Ω Ω ℝ)) = Real.exp t • 1 := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix Ω Ω ℝ) t
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using h.symm

theorem finiteChainSemigroup_uniformization (K : Matrix Ω Ω ℝ) (t : ℝ) :
    finiteChainSemigroup K t = Real.exp (-t) • NormedSpace.exp (t • K) := by
  have hcomm : Commute ((-t) • (1 : Matrix Ω Ω ℝ)) (t • K) :=
    ((Commute.one_left K).smul_left (-t)).smul_right t
  have heq : t • finiteChainGenerator K = (-t) • (1 : Matrix Ω Ω ℝ) + t • K := by
    simp only [finiteChainGenerator, smul_sub, neg_smul]
    abel
  unfold finiteChainSemigroup
  rw [heq, Matrix.exp_add_of_commute _ _ hcomm, matrix_exp_smul_one,
    Matrix.smul_mul, one_mul]

@[simp] theorem finiteChainSemigroup_zero (K : Matrix Ω Ω ℝ) :
    finiteChainSemigroup K 0 = 1 := by simp [finiteChainSemigroup]

theorem finiteChainSemigroup_add (K : Matrix Ω Ω ℝ) (s t : ℝ) :
    finiteChainSemigroup K (s + t) =
      finiteChainSemigroup K s * finiteChainSemigroup K t := by
  unfold finiteChainSemigroup
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl (finiteChainGenerator K)).smul_left s).smul_right t)

theorem matrix_exp_smul_hasSum (K : Matrix Ω Ω ℝ) (t : ℝ) (x y : Ω) :
    HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * t ^ k * (K ^ k) x y)
      (NormedSpace.exp (t • K) x y) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • K)
  have hxy := Pi.hasSum.mp (Pi.hasSum.mp h x) y
  simpa only [smul_pow, smul_smul, Matrix.smul_apply, smul_eq_mul, mul_assoc] using hxy

theorem matrix_exp_smul_nonneg (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (t : ℝ) (ht : 0 ≤ t) (x y : Ω) :
    0 ≤ NormedSpace.exp (t • K) x y := by
  rw [← (matrix_exp_smul_hasSum K t x y).tsum_eq]
  apply tsum_nonneg
  intro k
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg ht k))
    (Matrix.nonneg_of_mem_rowStochastic ((Matrix.rowStochastic ℝ Ω).pow_mem hK k))

theorem matrix_exp_smul_row_sum (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (t : ℝ) (x : Ω) :
    (∑ y : Ω, NormedSpace.exp (t • K) x y) = Real.exp t := by
  have hrows := hasSum_sum (s := Finset.univ)
    (fun y _ => matrix_exp_smul_hasSum K t x y)
  have hcoeff : ∀ k : ℕ,
      (∑ y : Ω, (k.factorial : ℝ)⁻¹ * t ^ k * (K ^ k) x y) =
        (k.factorial : ℝ)⁻¹ * t ^ k := by
    intro k
    rw [← Finset.mul_sum,
      Matrix.sum_row_of_mem_rowStochastic ((Matrix.rowStochastic ℝ Ω).pow_mem hK k), mul_one]
  have hr : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * t ^ k)
      (∑ y : Ω, NormedSpace.exp (t • K) x y) := by
    simpa only [hcoeff] using hrows
  have he : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * t ^ k) (Real.exp t) := by
    simpa only [← Real.exp_eq_exp_ℝ, smul_eq_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) t)
  exact hr.unique he

theorem finiteChainSemigroup_stochastic (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (t : ℝ) (ht : 0 ≤ t) :
    finiteChainSemigroup K t ∈ Matrix.rowStochastic ℝ Ω := by
  apply Matrix.mem_rowStochastic_iff_sum.mpr
  rw [finiteChainSemigroup_uniformization]
  constructor
  · intro x y
    exact mul_nonneg (Real.exp_pos (-t)).le (matrix_exp_smul_nonneg K hK t ht x y)
  · intro x
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, matrix_exp_smul_row_sum K hK t]
    rw [← Real.exp_add]
    simp

theorem finiteChain_pow_detailed_balance (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x) :
    ∀ k : ℕ, ∀ x y, pi x * (K ^ k) x y = pi y * (K ^ k) y x := by
  intro k
  induction k with
  | zero =>
      intro x y
      by_cases hxy : x = y
      · subst y
        rfl
      · simp [hxy, Ne.symm hxy]
  | succ k ih =>
      intro x y
      calc
        pi x * (K ^ (k + 1)) x y =
            ∑ z, pi x * (K ^ k) x z * K z y := by
          rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = ∑ z, pi y * K y z * (K ^ k) z x := by
          apply Finset.sum_congr rfl
          intro z _
          rw [ih x z]
          calc
            pi z * (K ^ k) z x * K z y = (pi z * K z y) * (K ^ k) z x := by ring
            _ = (pi y * K y z) * (K ^ k) z x := by rw [hbalance z y]
        _ = pi y * (K ^ (k + 1)) y x := by
          rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          ring

theorem matrix_exp_smul_detailed_balance (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (t : ℝ) (x y : Ω) :
    pi x * NormedSpace.exp (t • K) x y =
      pi y * NormedSpace.exp (t • K) y x := by
  have hx := (matrix_exp_smul_hasSum K t x y).mul_left (pi x)
  have hy := (matrix_exp_smul_hasSum K t y x).mul_left (pi y)
  have hterm : ∀ k : ℕ,
      pi x * ((k.factorial : ℝ)⁻¹ * t ^ k * (K ^ k) x y) =
        pi y * ((k.factorial : ℝ)⁻¹ * t ^ k * (K ^ k) y x) := by
    intro k
    calc
      pi x * ((k.factorial : ℝ)⁻¹ * t ^ k * (K ^ k) x y) =
          ((k.factorial : ℝ)⁻¹ * t ^ k) * (pi x * (K ^ k) x y) := by ring
      _ = ((k.factorial : ℝ)⁻¹ * t ^ k) * (pi y * (K ^ k) y x) := by
        rw [finiteChain_pow_detailed_balance K pi hbalance k x y]
      _ = pi y * ((k.factorial : ℝ)⁻¹ * t ^ k * (K ^ k) y x) := by ring
  exact (hx.congr_fun (fun k => (hterm k).symm)).unique hy

theorem finiteChainSemigroup_detailed_balance (K : Matrix Ω Ω ℝ) (pi : Ω → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (t : ℝ) (x y : Ω) :
    pi x * finiteChainSemigroup K t x y = pi y * finiteChainSemigroup K t y x := by
  rw [finiteChainSemigroup_uniformization]
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    pi x * (Real.exp (-t) * NormedSpace.exp (t • K) x y) =
        Real.exp (-t) * (pi x * NormedSpace.exp (t • K) x y) := by ring
    _ = Real.exp (-t) * (pi y * NormedSpace.exp (t • K) y x) := by
      rw [matrix_exp_smul_detailed_balance K pi hbalance t x y]
    _ = pi y * (Real.exp (-t) * NormedSpace.exp (t • K) y x) := by ring

theorem finiteChainSemigroup_stationary (K : Matrix Ω Ω ℝ)
    (hK : K ∈ Matrix.rowStochastic ℝ Ω) (pi : Ω → ℝ)
    (hbalance : ∀ x y, pi x * K x y = pi y * K y x)
    (t : ℝ) (ht : 0 ≤ t) (y : Ω) :
    (∑ x, pi x * finiteChainSemigroup K t x y) = pi y := by
  calc
    (∑ x, pi x * finiteChainSemigroup K t x y) =
        ∑ x, pi y * finiteChainSemigroup K t y x :=
      Finset.sum_congr rfl (fun x _ => finiteChainSemigroup_detailed_balance K pi hbalance t x y)
    _ = pi y * ∑ x, finiteChainSemigroup K t y x := by rw [Finset.mul_sum]
    _ = pi y := by
      rw [Matrix.sum_row_of_mem_rowStochastic (finiteChainSemigroup_stochastic K hK t ht)]
      ring

end SKConstants
