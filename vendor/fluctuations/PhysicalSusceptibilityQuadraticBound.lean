module

public import PhysicalOverlapBandDecomposition

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem quadratic_le_hilbert_schmidt {I : Type*} [Fintype I]
    (A : Matrix I I ℝ) (v : I → ℝ) :
    (∑ i, ∑ j, A i j * v i * v j) ≤
      (∑ i, (v i)^2) * Real.sqrt (∑ i, ∑ j, (A i j)^2) := by
  classical
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun p : I × I => A p.1 p.2) (fun p : I × I => v p.1 * v p.2)
  simp only [Fintype.sum_prod_type] at h
  have hv : (∑ i, ∑ j, (v i * v j)^2) = (∑ i, (v i)^2)^2 := by
    rw [pow_two, Finset.sum_mul]
    simp only [mul_pow, Finset.mul_sum]
  rw [hv, Real.sqrt_sq (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

theorem physical_centered_spin_sqnorm_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) (sigma : Spin n) :
    (∑ i, (normalizedSpin n sigma i - actualSpinMean n steps x i)^2) ≤ 4 := by
  have hnorm : projectionEuclideanNorm n
      (fun i => normalizedSpin n sigma i - actualSpinMean n steps x i) ≤ 2 := by
    apply projectionEuclideanNorm_le_of_coordinate_bound n _ (by norm_num)
    intro i
    have hspin : |normalizedSpin n sigma i| = 1 / Real.sqrt (n : ℝ) := by
      simp only [normalizedSpin, abs_div, abs_spinValue, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h := (abs_sub _ _).trans (add_le_add (le_of_eq hspin) (actualSpinMean_abs_le n steps ha x i))
    convert h using 1 <;> ring
  have h := (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mp hnorm
  norm_num at h
  exact h

theorem physicalSusceptibility_le_trace_sqrt (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    physicalSusceptibility n steps x p ≤ 4 * Real.sqrt
      (∑ i, ∑ j, (LaplaceWindowFormalization.hierarchySourceHessianMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x i j)^2) := by
  let v := fun i => normalizedSpin n (ForwardPath.spin steps.length p) i - actualSpinMean n steps x i
  have h := LaplaceWindowFormalization.hierarchySourceHessianMatrix_quadratic
    (uniformWeight_pos n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
    steps ha x v
  have hproj : LaplaceWindowFormalization.physicalNormalizedSourceMap n v =
      fieldProjectionDirection n v := rfl
  rw [hproj] at h
  change gaussianHierarchyHessian _ _ steps x (fieldProjectionDirection n v) (fieldProjectionDirection n v) ≤ _
  rw [← h]
  have hquad := quadratic_le_hilbert_schmidt
    (LaplaceWindowFormalization.hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (LaplaceWindowFormalization.physicalNormalizedSourceMap n) steps x) v
  have heq : (v ⬝ᵥ ((LaplaceWindowFormalization.hierarchySourceHessianMatrix
      (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
      steps x).mulVec v)) = ∑ i, ∑ j,
      LaplaceWindowFormalization.hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
        (LaplaceWindowFormalization.physicalNormalizedSourceMap n) steps x i j * v i * v j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  apply hquad.trans
  exact mul_le_mul_of_nonneg_right (physical_centered_spin_sqnorm_le n steps ha x
    (ForwardPath.spin steps.length p)) (Real.sqrt_nonneg _)

end OAI.SKFluctuations
