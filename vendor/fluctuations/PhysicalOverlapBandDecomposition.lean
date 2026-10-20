module

public import ComparisonDirectConcentration
public import PhysicalSusceptibilityTrace

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

namespace FiniteSpinCovariance

variable {S I : Type*} [Fintype S] [Fintype I]

theorem overlapSecond_le_fourth_mean_and_cov (p : S → ℝ) (z : S → I → ℝ) :
    overlapSecond p z ≤ 2 * (meanSq p z)^2 + 2 * traceCovSq p z := by
  classical
  rw [overlapSecond_eq_second]
  calc
    _ ≤ ∑ i, ∑ j, (2 * (mean p z i * mean p z j)^2 + 2 * (cov p z i j)^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have he : second p z i j = cov p z i j + mean p z i * mean p z j := by
        unfold cov
        ring
      rw [he]
      nlinarith [sq_nonneg (cov p z i j - mean p z i * mean p z j)]
    _ = 2 * (meanSq p z)^2 + 2 * traceCovSq p z := by
      unfold meanSq traceCovSq
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, mul_pow]

end FiniteSpinCovariance

theorem hierarchy_overlap_second_le_fourth_mean {S I J : Type*}
    [Fintype S] [Nonempty S] [Fintype I] [Fintype J]
    {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (J → ℝ) →L[ℝ] ℝ) (z : S → I → ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J → ℝ) :
    hierarchyPairMean w phi (fun s t => (∑ i, z s i * z t i)^2) steps x ≤
      2 * (∑ i, (hierarchyVectorMean w phi z steps x i)^2)^2 +
        2 * hierarchyVectorTraceCovSq w phi z steps x := by
  rw [hierarchyVectorTraceCovSq_eq_atoms hw phi z steps ha x,
    hierarchyVectorMean_eq_atoms hw phi z steps ha x]
  simpa only [hierarchyPairMean, FiniteSpinCovariance.overlapSecond,
    FiniteSpinCovariance.meanSq, mul_comm] using
    FiniteSpinCovariance.overlapSecond_le_fourth_mean_and_cov
      (fun s => hierarchyAtom w phi steps s x) z

theorem physical_overlap_second_le_fourth_mean (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau)^2) steps x ≤
      2 * (∑ i, (actualSpinMean n steps x i)^2)^2 +
        2 * physicalSpinTraceCovSq n steps x := by
  simpa only [orderedOverlap_normalized, actualSpinMean, hierarchyVectorMean,
    hierarchyVectorTraceCovSq, physicalSpinTraceCovSq, physicalSpinCovariance] using
    hierarchy_overlap_second_le_fourth_mean (uniformWeight_pos n) (finiteFeature n)
      (normalizedSpin n) steps ha x

theorem physicalSpinTraceCovSq_le_sourceHessian (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (ha0 : 0 < a) (x : FeatureIndex n → ℝ) :
    physicalSpinTraceCovSq n steps x ≤
      (∑ i, ∑ j, (LaplaceWindowFormalization.hierarchySourceHessianMatrix
        (uniformWeight n) (finiteFeature n)
        (LaplaceWindowFormalization.physicalNormalizedSourceMap n) steps x i j)^2) / a^2 := by
  have h := (LaplaceWindowFormalization.physicalSourceCovarianceHessian_trace
    n steps ha ha0 x).2
  rw [LaplaceWindowFormalization.physicalSourceCovarianceMatrix_eq_entries] at h
  exact h

end OAI.SKFluctuations
