module

public import PhysicalSusceptibilityMean
public import PhysicalSusceptibilityQuadraticBound
public import PhysicalSourceTraceBounds

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalSusceptibility_le_four (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ)
    (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
    physicalSusceptibility n steps x p ≤ 4 := by
  have h := physicalSusceptibility_le_trace_sqrt n steps ha x p
  have htrace := LaplaceWindowFormalization.physicalSourceHessianMatrix_entry_squares_le_one
    n steps ha x
  have hsqrt := Real.sqrt_le_sqrt htrace
  rw [Real.sqrt_one] at hsqrt
  linarith

theorem physicalSusceptibility_integral_eq_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    (∫ p, physicalSusceptibility n steps x p
      ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps x) =
      (LaplaceWindowFormalization.hierarchySourceHessianMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x * LaplaceWindowFormalization.hierarchySourceCovarianceMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x).trace := by
  have he (p : ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) :
      physicalSusceptibility n steps x p = physicalThermalSusceptibility n steps x
        (ForwardPath.spin steps.length p) := rfl
  simp_rw [he]
  rw [integral_hierarchyPathKernel (uniformWeight_pos n) (finiteFeature n)
    (physicalThermalSusceptibility n steps x) steps ha x,
    physicalThermalSusceptibility_mean_eq_trace n steps ha x]

theorem physicalSusceptibility_rooted_integral_eq_trace (n : ℕ)
    (q₀ : FeatureIndex n → ℝ≥0) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) :
    (∫ p, physicalSusceptibility n steps p.1 p.2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) =
      (∫ x, (LaplaceWindowFormalization.hierarchySourceHessianMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x * LaplaceWindowFormalization.hierarchySourceCovarianceMatrix
        (uniformWeight n) (finiteFeature n) (LaplaceWindowFormalization.physicalNormalizedSourceMap n)
        steps x).trace ∂Measure.pi (fun k => gaussianReal 0 (q₀ k))) := by
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ steps ha
  have hI : Integrable (fun p => physicalSusceptibility n steps p.1 p.2)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
    apply (integrable_const (4 : ℝ)).mono'
      (physicalSusceptibility_measurable n steps ha id measurable_id).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact physicalSusceptibility_le_four n steps ha p.1 p.2
      · exact gaussianHierarchyHessian_nonneg (uniformWeight_pos n) (finiteFeature n) steps ha p.1 _
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  rw [rootedHierarchyPathLaw, Measure.integral_compProd hI]
  simp_rw [physicalSusceptibility_integral_eq_trace n steps ha]

end OAI.SKFluctuations
