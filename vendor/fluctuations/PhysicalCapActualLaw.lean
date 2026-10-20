module

public import PhysicalCapTraceTransport
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalPinnedWindow

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalSpinMeanSq_eq_pairMean (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) :
    physicalSpinMeanSq n steps x =
      hierarchyPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) steps x := by
  rw [hierarchyPairMean_overlap_eq_norm n steps ha, EuclideanSpace.norm_sq_eq]
  simp only [physicalSpinMeanSq, actualSpinMean, Real.norm_eq_abs, sq_abs]

theorem physicalPrefixMeanSq_eq_pathSecondMoment (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre ++ tail)) (q₀ : FeatureIndex n → ℝ≥0) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (prefixTest pre (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
        (physicalSpinMeanSq n tail)) 0 =
      physicalPathSecondMoment n (pre ++ tail) q₀ pre.length := by
  rw [physicalSecondMoment_eq_rootLevelPairMean n (pre ++ tail) ha q₀ pre.length
    (by simp)]
  unfold rootLevelPairMean
  rw [levelPairMean_prefix]
  have he := funext (physicalSpinMeanSq_eq_pairMean n tail (ha.suffix pre tail))
  rw [he]

theorem physicalPrefixTest_eq_rootedCutExpectation (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre ++ tail)) (q₀ : FeatureIndex n → ℝ≥0)
    (B : (FeatureIndex n → ℝ) → ℝ) (hB : BddSmooth 0 B) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (prefixTest pre (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail) B) 0 =
      ∫ p, B (actualCutField (S := Spin n) pre tail p.1 p.2)
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre ++ tail) ha
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ (pre ++ tail) ha
  have hI : Integrable (fun p => B (actualCutField (S := Spin n) pre tail p.1 p.2))
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail)) :=
    hB.integrable_comp_measurable (actualCutField_measurable_joint pre tail)
  rw [rootedHierarchyPathLaw, Measure.integral_compProd hI]
  simp_rw [integral_actualCutField_test (uniformWeight_pos n) (finiteFeature n) pre tail ha hB]
  simp only [zeroContinuation, zero_add]

theorem physicalFiniteCapEnergy_rooted_eq_path_increment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q₀ : FeatureIndex n → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre ++ tail)) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapEnergy n d e pre tail ha) 0 =
      physicalPathSecondMoment n (pre ++ tail) q₀ pre.length -
      physicalPathSecondMoment n (pre ++ tail) q₀ 0 := by
  rw [physicalFiniteCapEnergy_rooted_eq_increment,
    physicalPrefixMeanSq_eq_pathSecondMoment n pre tail ha q₀]
  have hzero := physicalPrefixMeanSq_eq_pathSecondMoment n [] (pre ++ tail) ha q₀
  simpa only [prefixTest, List.length_nil, List.nil_append] using congrArg
    (fun z => physicalPathSecondMoment n (pre ++ tail) q₀ pre.length - z) hzero

theorem physicalFiniteCapRadiusTrace_rooted_le_pathSecondMoment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (q₀ : FeatureIndex (n + 1) → ℝ≥0)
    (duration : GaussianStep (FeatureIndex (n + 1)) → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {g M : ℝ}
    (ha : OrderedSteps 0 (pre ++ tail)) (hg : 0 < g)
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : ∀ st ∈ pre, g * duration st ≤ st.2 (Sum.inl 0))
    (hmean : physicalPathSecondMoment (n + 1) (pre ++ tail) q₀ pre.length ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapRadiusTrace n d e duration pre tail ha) 0 ≤ M / ((n + 1 : ℝ) * g) := by
  apply physicalFiniteCapRadiusTrace_rooted_le_endpoint n d e q₀ duration pre tail ha hg hfield hslope 0
  exact (physicalPrefixMeanSq_eq_pathSecondMoment (n + 1) pre tail ha q₀).le.trans hmean

end
end OAI.SKFluctuations.LaplaceWindowFormalization
