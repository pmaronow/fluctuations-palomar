module

public import PhysicalSusceptibilityTrace

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy Matrix
open scoped Topology NNReal BigOperators

theorem normalizedSpin_square_sum_le_one (n : ℕ) (sigma : Spin n) :
    (∑ i, (normalizedSpin n sigma i)^2) ≤ 1 := by
  have hnorm : projectionEuclideanNorm n (normalizedSpin n sigma) ≤ 1 := by
    apply projectionEuclideanNorm_le_of_coordinate_bound n _ zero_le_one
    intro i
    simp only [normalizedSpin, abs_div, abs_spinValue, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact le_rfl
  have h := (Real.sqrt_le_left zero_le_one).mp hnorm
  norm_num at h
  exact h

theorem physicalSourceCovarianceMatrix_trace_le_one (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    (hierarchySourceCovarianceMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x).trace ≤ 1 := by
  let Z (sigma : Spin n) := ∑ i, (normalizedSpin n sigma i)^2
  have hZ : ∀ sigma, |Z sigma| ≤ 1 := by
    intro sigma
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact normalizedSpin_square_sum_le_one n sigma
  have hmean := gaussianHierarchyMean_abs_le (uniformWeight_pos n) (finiteFeature n)
    hZ steps ha x
  have hmean' : gaussianHierarchyMean (uniformWeight n) (finiteFeature n) Z steps x ≤ 1 :=
    (le_abs_self _).trans hmean
  rw [physicalSourceCovarianceMatrix_eq_entries]
  simp only [Matrix.trace, Matrix.diag, hierarchyCovariance, ← pow_two,
    Finset.sum_sub_distrib]
  have hsum := congrFun (gaussianHierarchyMean_sum (uniformWeight_pos n) (finiteFeature n)
    steps ha Finset.univ (fun i sigma => (normalizedSpin n sigma i)^2)) x
  have hsq : 0 ≤ ∑ i, (gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (fun sigma => normalizedSpin n sigma i) steps x)^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  change gaussianHierarchyMean (uniformWeight n) (finiteFeature n) Z steps x = _ at hsum
  linarith

theorem physicalSourceHessianMatrix_trace_le_one (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    (hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x).trace ≤ 1 := by
  obtain ⟨_, _, _, hCH⟩ := physicalSourceCovarianceHessian_psd n steps ha x
  have h := hCH.trace_nonneg
  rw [Matrix.trace_sub] at h
  have hc := physicalSourceCovarianceMatrix_trace_le_one n steps ha x
  linarith

theorem physicalSourceHessianMatrix_entry_squares_le_one (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    (∑ i, ∑ j, (hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x i j)^2) ≤ 1 := by
  exact posSemidef_entry_squares_le_one
    (physicalSourceCovarianceHessian_psd n steps ha x).2.1
    (physicalSourceHessianMatrix_trace_le_one n steps ha x)

end OAI.SKFluctuations.LaplaceWindowFormalization
