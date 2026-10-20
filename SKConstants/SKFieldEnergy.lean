module

public import SKConstants.SKSparseFieldGeometry

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace Classical Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def spinMatrixField {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n)
    (i : Fin n) : ℝ := ∑ j, W i j * signedSpin x j

theorem quadraticHamiltonian_difference_expansion {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsSymm) (x y : Spin n) :
    quadraticHamiltonian W y - quadraticHamiltonian W x =
      inner (𝕜 := ℝ) (spinEuclidean y - spinEuclidean x)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) W (spinEuclidean x)) +
      (1 / 2) * inner (𝕜 := ℝ) (spinEuclidean y - spinEuclidean x)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) W (spinEuclidean y - spinEuclidean x)) := by
  let d := spinEuclidean y - spinEuclidean x
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) W
  have he : spinEuclidean y = spinEuclidean x + d := by dsimp [d]; abel
  have hs : inner (𝕜 := ℝ) (spinEuclidean x) (A d) =
      inner (𝕜 := ℝ) d (A (spinEuclidean x)) := by
    simp only [A, Matrix.inner_toEuclideanCLM]
    exact hW.dotProduct_mulVec_comm
  rw [quadraticHamiltonian_eq_inner, quadraticHamiltonian_eq_inner, he]
  simp only [map_add, inner_add_left, inner_add_right, add_sub_cancel_left]
  rw [hs]
  dsimp only [d, A]
  ring

theorem quadraticHamiltonian_hamming_sparse_field_bound {n r : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsSymm) (x y : Spin n)
    (hxy : hammingDist x y ≤ r) (A : ℝ)
    (hfields : ∀ I : Finset (Fin n), I.card ≤ r →
      ∑ i ∈ I, |spinMatrixField W x i| ≤ A) :
    |quadraticHamiltonian W y - quadraticHamiltonian W x| ≤ 2 * A + 2 * ‖W‖ * (r : ℝ) := by
  let d := spinEuclidean y - spinEuclidean x
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) W
  let I := spinDifferenceSet x y
  have hI : I.card ≤ r := hxy
  have hcross : |inner (𝕜 := ℝ) d (L (spinEuclidean x))| ≤ 2 * A := by
    rw [Matrix.inner_toEuclideanCLM]
    change |∑ i, (signedSpin y i - signedSpin x i) * spinMatrixField W x i| ≤ 2 * A
    rw [← Finset.sum_subset (Finset.subset_univ I) (fun i hi hiI => ?_)]
    · calc
        _ ≤ ∑ i ∈ I, |(signedSpin y i - signedSpin x i) * spinMatrixField W x i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ I, 2 * |spinMatrixField W x i| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          have hd : |signedSpin y i - signedSpin x i| ≤ (2 : ℝ) := by
            cases hy : y i <;> cases hx : x i <;> norm_num [signedSpin, hy, hx]
          exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
        _ ≤ 2 * A := by rw [← Finset.mul_sum]; linarith [hfields I hI]
    · have he : x i = y i := by
        simpa only [I, spinDifferenceSet, Finset.mem_filter, Finset.mem_univ,
          true_and, not_not] using hiI
      simp [signedSpin, he]
  have hquad : |inner (𝕜 := ℝ) d (L d)| ≤ 4 * ‖W‖ * (r : ℝ) := by
    have hop := L.le_opNorm d
    rw [show ‖L‖ = ‖W‖ from Matrix.l2_opNorm_toEuclideanCLM W] at hop
    have h := (abs_real_inner_le_norm d (L d)).trans
      (mul_le_mul_of_nonneg_left hop (norm_nonneg d))
    have hd : ‖d‖^2 ≤ 4 * (r : ℝ) := by
      rw [show ‖d‖^2 = 4 * (hammingDist y x : ℝ) from spinEuclidean_distance_sq y x,
        hammingDist_comm y x]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hxy) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg W)]
  rw [quadraticHamiltonian_difference_expansion W hW]
  calc
    _ ≤ |inner (𝕜 := ℝ) d (L (spinEuclidean x))| +
        |(1 / 2 : ℝ) * inner (𝕜 := ℝ) d (L d)| := abs_add_le _ _
    _ ≤ 2 * A + 2 * ‖W‖ * (r : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      linarith

theorem sk_energy_difference_outside_sparseFieldBadSet {n r : ℕ} (x y : Spin n)
    (hxy : hammingDist x y ≤ r) (A : ℝ) (z : EuclideanSpace ℝ (Fin n × Fin n))
    (hz : z ∉ sparseFieldBadSet x r A) :
    |quadraticHamiltonian (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z) y -
      quadraticHamiltonian (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z) x| ≤
      2 * A + 2 * ‖GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z‖ * (r : ℝ) := by
  apply quadraticHamiltonian_hamming_sparse_field_bound _ (GaussianProposal.goeMatrix_symmetric _ _) x y hxy A
  intro I hI
  exact (sparseFieldBadSet_controls_absolute_sums x A z hz I hI).le

end SKConstants
