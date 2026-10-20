module

public import PhysicalOverlapBandDecomposition

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

namespace FiniteSpinCovariance

variable {S I : Type*} [Fintype S] [Fintype I]

theorem centered_second (p : S → ℝ) (z : S → I → ℝ) (hpsum : ∑ s, p s = 1)
    (i j : I) :
    (∑ s, p s * ((z s i - mean p z i) * (z s j - mean p z j))) = cov p z i j := by
  classical
  have he (s : S) :
      p s * ((z s i - mean p z i) * (z s j - mean p z j)) =
      p s * z s i * z s j - mean p z j * (p s * z s i) -
        mean p z i * (p s * z s j) + p s * (mean p z i * mean p z j) := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hpsum]
  change second p z i j - mean p z j * mean p z i -
    mean p z i * mean p z j + 1 * (mean p z i * mean p z j) = cov p z i j
  unfold cov
  ring

theorem mean_centered_quadratic (p : S → ℝ) (z : S → I → ℝ)
    (hpsum : ∑ s, p s = 1) (H : Matrix I I ℝ) :
    (∑ s, p s * (∑ i, ∑ j, H i j * (z s i - mean p z i) * (z s j - mean p z j))) =
      ∑ i, ∑ j, H i j * cov p z i j := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he (s : S) : p s * (H i j * (z s i - mean p z i) * (z s j - mean p z j)) =
      H i j * (p s * ((z s i - mean p z i) * (z s j - mean p z j))) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, centered_second p z hpsum]

end FiniteSpinCovariance

def physicalThermalSusceptibility (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ)
    (sigma : Spin n) : ℝ :=
  let v := fun i => normalizedSpin n sigma i - actualSpinMean n steps x i
  gaussianHierarchyHessian (uniformWeight n) (finiteFeature n) steps x
    (fieldProjectionDirection n v) (fieldProjectionDirection n v)

theorem physicalThermalSusceptibility_eq_quadratic (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) (sigma : Spin n) :
    physicalThermalSusceptibility n steps x sigma =
      ∑ i, ∑ j, LaplaceWindowFormalization.hierarchySourceHessianMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x i j * (normalizedSpin n sigma i - actualSpinMean n steps x i) *
          (normalizedSpin n sigma j - actualSpinMean n steps x j) := by
  let v := fun i => normalizedSpin n sigma i - actualSpinMean n steps x i
  have he := LaplaceWindowFormalization.hierarchySourceHessianMatrix_quadratic
    (uniformWeight_pos n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
      steps ha x v
  have hproj : LaplaceWindowFormalization.physicalNormalizedSourceMap n v =
      fieldProjectionDirection n v := rfl
  rw [hproj] at he
  rw [physicalThermalSusceptibility]
  rw [← he]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, v]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem physicalThermalSusceptibility_mean_eq_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (physicalThermalSusceptibility n steps x) steps x =
      (LaplaceWindowFormalization.hierarchySourceHessianMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x * LaplaceWindowFormalization.hierarchySourceCovarianceMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x).trace := by
  let p := fun sigma => hierarchyAtom (uniformWeight n) (finiteFeature n) steps sigma x
  let H := LaplaceWindowFormalization.hierarchySourceHessianMatrix
    (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n) steps x
  have hmean := hierarchyVectorMean_eq_atoms (uniformWeight_pos n) (finiteFeature n)
    (normalizedSpin n) steps ha x
  have heX : actualSpinMean n steps x = FiniteSpinCovariance.mean p (normalizedSpin n) := hmean
  rw [gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) steps ha]
  simp_rw [physicalThermalSusceptibility_eq_quadratic n steps ha x, heX]
  have h := FiniteSpinCovariance.mean_centered_quadratic p (normalizedSpin n)
    (hierarchyAtom_sum (uniformWeight_pos n) (finiteFeature n) steps ha x) H
  have h' : (∑ sigma, (∑ i, ∑ j, H i j *
      (normalizedSpin n sigma i - FiniteSpinCovariance.mean p (normalizedSpin n) i) *
      (normalizedSpin n sigma j - FiniteSpinCovariance.mean p (normalizedSpin n) j)) * p sigma) =
      ∑ i, ∑ j, H i j * FiniteSpinCovariance.cov p (normalizedSpin n) i j := by
    simpa only [mul_comm] using h
  rw [h']
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [LaplaceWindowFormalization.hierarchySourceCovarianceMatrix,
    LaplaceWindowFormalization.physicalNormalizedSourceMap_feature,
    hierarchyCovariance, FiniteSpinCovariance.cov, FiniteSpinCovariance.second,
    FiniteSpinCovariance.mean, p,
    gaussianHierarchyMean_atoms (uniformWeight_pos n) (finiteFeature n) steps ha]
  congr 1
  · apply Finset.sum_congr rfl
    intro sigma _
    ring
  · simp only [mul_comm]

theorem physicalThermalSusceptibility_mean_le_sourceHessian (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (ha0 : 0 < a) (x : FeatureIndex n → ℝ) :
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n)
      (physicalThermalSusceptibility n steps x) steps x ≤
      (∑ i, ∑ j, (LaplaceWindowFormalization.hierarchySourceHessianMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x i j)^2) / a := by
  rw [physicalThermalSusceptibility_mean_eq_trace n steps ha x]
  exact (LaplaceWindowFormalization.physicalSourceCovarianceHessian_trace
    n steps ha ha0 x).1

end OAI.SKFluctuations
