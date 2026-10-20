module

public import SKConstants.GibbsVariational
public import SKConstants.EuclideanMatrix

public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace SKConstants

theorem gibbsPartition_comparison {n : ℕ} (beta L : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℝ)
    (henergy : ∀ x, |quadraticHamiltonian W x - quadraticHamiltonian V x| ≤ L) :
    gibbsPartition beta W ≤ Real.exp (|beta| * L) * gibbsPartition beta V := by
  unfold gibbsPartition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hab : |beta * (quadraticHamiltonian W x - quadraticHamiltonian V x)| ≤
      |beta| * L := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (henergy x) (abs_nonneg beta)
  have hb := (le_abs_self (beta * (quadraticHamiltonian W x -
    quadraticHamiltonian V x))).trans hab
  linarith

theorem gibbsPressure_comparison {n : ℕ} (beta L : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℝ)
    (henergy : ∀ x, |quadraticHamiltonian W x - quadraticHamiltonian V x| ≤ L) :
    |Real.log (gibbsPartition beta W) - Real.log (gibbsPartition beta V)| ≤
      |beta| * L := by
  have hupper := Real.log_le_log (gibbsPartition_pos beta W)
    (gibbsPartition_comparison beta L W V henergy)
  rw [Real.log_mul (Real.exp_ne_zero _) (gibbsPartition_pos beta V).ne',
    Real.log_exp] at hupper
  have hreverse : ∀ x, |quadraticHamiltonian V x - quadraticHamiltonian W x| ≤ L := by
    intro x
    simpa only [abs_sub_comm] using henergy x
  have hlower := Real.log_le_log (gibbsPartition_pos beta V)
    (gibbsPartition_comparison beta L V W hreverse)
  rw [Real.log_mul (Real.exp_ne_zero _) (gibbsPartition_pos beta W).ne',
    Real.log_exp] at hlower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem gibbs_log_ratio_comparison {n : ℕ} (beta L : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℝ)
    (henergy : ∀ x, |quadraticHamiltonian W x - quadraticHamiltonian V x| ≤ L)
    (x : Spin n) :
    |Real.log (gibbsProbability beta W x / gibbsProbability beta V x)| ≤
      2 * |beta| * L := by
  rw [Real.log_div (gibbsProbability_pos beta W x).ne'
    (gibbsProbability_pos beta V x).ne', log_gibbsProbability, log_gibbsProbability]
  have hrewrite : beta * quadraticHamiltonian W x - Real.log (gibbsPartition beta W) -
      (beta * quadraticHamiltonian V x - Real.log (gibbsPartition beta V)) =
      beta * (quadraticHamiltonian W x - quadraticHamiltonian V x) -
        (Real.log (gibbsPartition beta W) - Real.log (gibbsPartition beta V)) := by ring
  rw [hrewrite]
  calc
    _ ≤ |beta * (quadraticHamiltonian W x - quadraticHamiltonian V x)| +
        |Real.log (gibbsPartition beta W) - Real.log (gibbsPartition beta V)| :=
      abs_sub _ _
    _ ≤ |beta| * L + |beta| * L := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (henergy x) (abs_nonneg beta))
        (gibbsPressure_comparison beta L W V henergy)
    _ = _ := by ring

theorem gibbsProbability_comparison {n : ℕ} (beta L : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℝ)
    (henergy : ∀ x, |quadraticHamiltonian W x - quadraticHamiltonian V x| ≤ L)
    (x : Spin n) :
    gibbsProbability beta W x ≤ Real.exp (2 * |beta| * L) * gibbsProbability beta V x := by
  have h := (le_abs_self _).trans (gibbs_log_ratio_comparison beta L W V henergy x)
  have he := (Real.log_le_iff_le_exp (div_pos
    (gibbsProbability_pos beta W x) (gibbsProbability_pos beta V x))).mp h
  exact (div_le_iff₀ (gibbsProbability_pos beta V x)).mp he

theorem gibbs_KL_comparison {n : ℕ} (beta L : ℝ)
    (W V : Matrix (Fin n) (Fin n) ℝ)
    (henergy : ∀ x, |quadraticHamiltonian W x - quadraticHamiltonian V x| ≤ L) :
    finiteKL (gibbsProbability beta W) (gibbsProbability beta V) ≤ 2 * |beta| * L := by
  unfold finiteKL
  calc
    _ ≤ ∑ x, gibbsProbability beta W x * (2 * |beta| * L) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans
        (gibbs_log_ratio_comparison beta L W V henergy x)) (gibbsProbability_pos beta W x).le
    _ = _ := by rw [← Finset.sum_mul, gibbsProbability_sum, one_mul]

@[expose] def spinEuclidean {n : ℕ} (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (signedSpin x)

theorem spinEuclidean_norm_sq {n : ℕ} (x : Spin n) : ‖spinEuclidean x‖ ^ 2 = n := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [spinEuclidean, signedSpin_sq]

theorem quadraticHamiltonian_eq_inner {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    quadraticHamiltonian W x = (1 / 2) * inner (𝕜 := ℝ) (spinEuclidean x)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W (spinEuclidean x)) := by
  rw [Matrix.inner_toEuclideanCLM]
  change (1 / 2 : ℝ) * (∑ i, ∑ j, signedSpin x i * W i j * signedSpin x j) =
    (1 / 2 : ℝ) * (∑ i, signedSpin x i * (∑ j, W i j * signedSpin x j))
  congr 1
  simp_rw [Finset.mul_sum, mul_assoc]

theorem quadraticHamiltonian_opNorm_bound {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    |quadraticHamiltonian W x| ≤ (n : ℝ) * ‖W‖ / 2 := by
  rw [quadraticHamiltonian_eq_inner, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hinner := abs_real_inner_le_norm (spinEuclidean x)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W (spinEuclidean x))
  have hop := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W).le_opNorm (spinEuclidean x)
  rw [Matrix.l2_opNorm_toEuclideanCLM] at hop
  have h := hinner.trans (mul_le_mul_of_nonneg_left hop (norm_nonneg _))
  have heq : ‖spinEuclidean x‖ * (‖W‖ * ‖spinEuclidean x‖) = (n : ℝ) * ‖W‖ := by
    calc
      _ = ‖spinEuclidean x‖ ^ 2 * ‖W‖ := by ring
      _ = _ := by rw [spinEuclidean_norm_sq]
  rw [heq] at h
  linarith

end SKConstants
