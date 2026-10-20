module

public import SKConstants.EntropyDissipation
public import SKConstants.MeasureEntropyCoverage

public section
noncomputable section
open scoped Classical

namespace SKConstants

theorem log_gibbsProbability {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    Real.log (gibbsProbability beta W x) =
      beta * quadraticHamiltonian W x - Real.log (gibbsPartition beta W) := by
  unfold gibbsProbability
  rw [Real.log_div (Real.exp_ne_zero _) (gibbsPartition_pos beta W).ne', Real.log_exp]

theorem finiteGibbs_entropy_energy_identity {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (q : Spin n → ℝ)
    (hq : ∀ x, 0 < q x) (hq_sum : ∑ x, q x = 1) :
    finiteKL q (gibbsProbability beta W) =
      Real.log (gibbsPartition beta W) -
        beta * (∑ x, q x * quadraticHamiltonian W x) - finiteShannonEntropy q := by
  have hpoint : ∀ x, q x * Real.log (q x / gibbsProbability beta W x) =
      q x * Real.log (q x) - beta * (q x * quadraticHamiltonian W x) +
        q x * Real.log (gibbsPartition beta W) := by
    intro x
    rw [Real.log_div (hq x).ne' (gibbsProbability_pos beta W x).ne',
      log_gibbsProbability]
    ring
  unfold finiteKL finiteShannonEntropy
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hq_sum, one_mul]
  ring

theorem finiteGibbs_variational_bound {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (q : Spin n → ℝ)
    (hq : ∀ x, 0 < q x) (hq_sum : ∑ x, q x = 1) :
    beta * (∑ x, q x * quadraticHamiltonian W x) + finiteShannonEntropy q ≤
      Real.log (gibbsPartition beta W) := by
  have h := finiteKL_nonneg q (gibbsProbability beta W) hq
    (gibbsProbability_pos beta W) hq_sum (gibbsProbability_sum beta W)
  rw [finiteGibbs_entropy_energy_identity beta W q hq hq_sum] at h
  linarith

end SKConstants
