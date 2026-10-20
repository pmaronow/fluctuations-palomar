module

public import SKConstants.EntropyCoverage
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Basic

public section
noncomputable section

namespace SKConstants

/-- A configuration of `n` Boolean spins. The finite space has `2^n` elements. -/
abbrev Spin (n : ℕ) := Fin n → Bool

/-- Interpret `true` as `+1` and `false` as `-1`. -/
@[expose] def signedSpin {n : ℕ} (x : Spin n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

/-- The completed quadratic spin Hamiltonian `H_W(x) = xᵀ W x / 2`.
No symmetry or probabilistic law for `W` is needed. -/
@[expose] def quadraticHamiltonian {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ i, ∑ j, signedSpin x i * W i j * signedSpin x j

/-- The actual finite partition function, with the inverse temperature
permitted to be any real number. -/
@[expose] def gibbsPartition {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ x : Spin n, Real.exp (beta * quadraticHamiltonian W x)

/-- The Gibbs probability of an individual spin configuration. -/
@[expose] def gibbsProbability {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  Real.exp (beta * quadraticHamiltonian W x) / gibbsPartition beta W

theorem signedSpin_sq {n : ℕ} (x : Spin n) (i : Fin n) :
    signedSpin x i ^ 2 = 1 := by
  cases h : x i <;> simp [signedSpin, h]

theorem gibbsPartition_pos {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : 0 < gibbsPartition beta W := by
  classical
  unfold gibbsPartition
  exact Finset.sum_pos (fun x _ ↦ Real.exp_pos (beta * quadraticHamiltonian W x))
    ⟨fun _ ↦ false, Finset.mem_univ _⟩

theorem gibbsProbability_pos {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    0 < gibbsProbability beta W x := by
  exact div_pos (Real.exp_pos _) (gibbsPartition_pos beta W)

theorem gibbsProbability_sum {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    ∑ x : Spin n, gibbsProbability beta W x = 1 := by
  classical
  unfold gibbsProbability
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gibbsPartition_pos beta W))

theorem finiteGibbs_positive_normalized (n : ℕ) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x : Spin n, 0 < gibbsProbability beta W x) ∧
      (∑ x : Spin n, gibbsProbability beta W x) = 1 := by
  exact ⟨gibbsProbability_pos beta W, gibbsProbability_sum beta W⟩

theorem quadraticHamiltonian_add {n : ℕ}
    (W M : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    quadraticHamiltonian (W + M) x =
      quadraticHamiltonian W x + quadraticHamiltonian M x := by
  simp only [quadraticHamiltonian, Matrix.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib]

theorem quadraticHamiltonian_diagonal {n : ℕ} (d : Fin n → ℝ) (x : Spin n) :
    quadraticHamiltonian (Matrix.diagonal d) x = (1 / 2) * ∑ i, d i := by
  classical
  have hdiag : ∀ i : Fin n,
      (∑ j, signedSpin x i * Matrix.diagonal d i j * signedSpin x j) = d i := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
      calc
        signedSpin x i * d i * signedSpin x i = d i * signedSpin x i ^ 2 := by ring
        _ = d i := by rw [signedSpin_sq]; ring
    · intro j _ hji
      rw [Matrix.diagonal_apply_ne d (Ne.symm hji)]
      simp
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp only [quadraticHamiltonian, hdiag]
  norm_num

theorem quadraticHamiltonian_add_diagonal {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (x : Spin n) :
    quadraticHamiltonian (W + Matrix.diagonal d) x =
      quadraticHamiltonian W x + (1 / 2) * ∑ i, d i := by
  rw [quadraticHamiltonian_add, quadraticHamiltonian_diagonal]

theorem gibbsProbability_constant_shift {n : ℕ} (beta c : ℝ)
    (W M : Matrix (Fin n) (Fin n) ℝ)
    (hShift : ∀ x : Spin n,
      quadraticHamiltonian M x = quadraticHamiltonian W x + c)
    (x : Spin n) : gibbsProbability beta M x = gibbsProbability beta W x := by
  classical
  have hPart : gibbsPartition beta M = Real.exp (beta * c) * gibbsPartition beta W := by
    unfold gibbsPartition
    calc
      (∑ x : Spin n, Real.exp (beta * quadraticHamiltonian M x)) =
          ∑ x : Spin n,
            Real.exp (beta * c) * Real.exp (beta * quadraticHamiltonian W x) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hShift, mul_add, Real.exp_add]
        ring
      _ = Real.exp (beta * c) *
          ∑ x : Spin n, Real.exp (beta * quadraticHamiltonian W x) := by
        rw [Finset.mul_sum]
  unfold gibbsProbability
  rw [hShift, hPart, mul_add, Real.exp_add]
  have hc : Real.exp (beta * c) ≠ 0 := Real.exp_ne_zero _
  have hZ : gibbsPartition beta W ≠ 0 := ne_of_gt (gibbsPartition_pos beta W)
  field_simp

theorem gibbsProbability_add_diagonal {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (x : Spin n) :
    gibbsProbability beta (W + Matrix.diagonal d) x = gibbsProbability beta W x := by
  exact gibbsProbability_constant_shift beta ((1 / 2) * ∑ i, d i)
    W (W + Matrix.diagonal d) (quadraticHamiltonian_add_diagonal W d) x

theorem finiteGibbs_entropy_coverage {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (q : Spin n → ℝ)
    (A : Finset (Spin n)) (K alpha : ℝ)
    (hq : ∀ x, 0 < q x) (hq_sum : ∑ x, q x = 1)
    (hKL : finiteKL (gibbsProbability beta W) q ≤ K)
    (hAlpha : 0 < alpha)
    (hMass : alpha ≤ ∑ x ∈ A, gibbsProbability beta W x) :
    Real.exp (-(K + Real.log 2) / alpha) ≤ ∑ x ∈ A, q x := by
  exact finiteKL_uniform_coverage (gibbsProbability beta W) q A K alpha
    (gibbsProbability_pos beta W) hq (gibbsProbability_sum beta W) hq_sum
    hKL hAlpha hMass

end SKConstants
