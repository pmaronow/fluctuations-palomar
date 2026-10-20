module

public import PhysicalBPathLimit

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalStepPairMoment_eq_rooted_massStepFunction (n : ℕ)
    (q₀ : FeatureIndex n → ℝ≥0) (steps : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 steps) (P : Spin n → Spin n → ℝ) [NeZero n] :
    stepPairMoment (uniformWeight n) (finiteFeature n) q₀ steps ha.mem_pos P =
      massStepFunction (positiveStepMasses steps ha.mem_pos)
        (fun j => rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀ P steps j) := by
  unfold stepPairMoment cumulativePair
  simp_rw [ClockTree.pairDisorder_eq_rootLevelPairMean (uniformWeight_pos n) (finiteFeature n)
    _ (positiveStepMasses_ordered ha ha.mem_pos)]
  simp only [stepClockValues_zero, Real.toNNReal_coe, diagonalBoundarySteps_stepClockValues]

theorem physicalSampledB_eq_rooted_massStepFunction (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    physicalSampledB n b h as ha =
      massStepFunction as (fun j => rootLevelPairMean (uniformWeight (n + 1))
        (finiteFeature (n + 1)) (completedPathClock (n + 1) b h 0)
        (fun σ τ => (orderedOverlap (n + 1) σ τ)^2)
        (sampleClockSteps (completedPathClock (n + 1) b h) 0 as) j) := by
  unfold physicalSampledB
  rw [physicalStepPairMoment_eq_rooted_massStepFunction (n + 1)
    (completedPathClock (n + 1) b h 0)
    (sampleClockSteps (completedPathClock (n + 1) b h) 0 as)
    (sampleClockSteps_ordered _ as ha)]
  rw [sampleClockSteps_masses]

theorem physicalSampledB_integral_eq_massStepSum (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    (∫ u in 0..1, physicalSampledB n b h as ha u) =
      massStepSum as 0 (fun j => rootLevelPairMean (uniformWeight (n + 1))
        (finiteFeature (n + 1)) (completedPathClock (n + 1) b h 0)
        (fun σ τ => (orderedOverlap (n + 1) σ τ)^2)
        (sampleClockSteps (completedPathClock (n + 1) b h) 0 as) j) := by
  rw [physicalSampledB_eq_rooted_massStepFunction]
  exact massStepFunction_integral as 0 _ ha

theorem physicalSampledB_weighted_integral_eq_massStepSum (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (weights : ℕ → ℝ) :
    (∫ u in 0..1, massStepFunction as weights u * physicalSampledB n b h as ha u) =
      massStepSum as 0 (fun j => weights j * rootLevelPairMean (uniformWeight (n + 1))
        (finiteFeature (n + 1)) (completedPathClock (n + 1) b h 0)
        (fun σ τ => (orderedOverlap (n + 1) σ τ)^2)
        (sampleClockSteps (completedPathClock (n + 1) b h) 0 as) j) := by
  rw [physicalSampledB_eq_rooted_massStepFunction]
  simp_rw [← massStepFunction_mul]
  exact massStepFunction_integral as 0 _ ha

theorem physicalRootLevelB_eq_actual_prefixTest (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (_ha : OrderedSteps 0 (pre ++ tail)) (q₀ : FeatureIndex n → ℝ≥0) :
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀
      (fun σ τ => (orderedOverlap n σ τ)^2) (pre ++ tail) pre.length =
      zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest pre (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
          (hierarchyPairMean (uniformWeight n) (finiteFeature n)
            (fun σ τ => (orderedOverlap n σ τ)^2) tail)) 0 := by
  rw [rootLevelPairMean, levelPairMean_prefix]

theorem physicalRootLevelB_eq_actual_cutExpectation (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre ++ tail)) (q₀ : FeatureIndex n → ℝ≥0) :
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀
      (fun σ τ => (orderedOverlap n σ τ)^2) (pre ++ tail) pre.length =
      ∫ p, hierarchyPairMean (uniformWeight n) (finiteFeature n)
        (fun σ τ => (orderedOverlap n σ τ)^2) tail (actualCutField pre tail p.1 p.2)
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail) := by
  rw [physicalRootLevelB_eq_actual_prefixTest n pre tail ha q₀]
  exact physicalPrefixTest_eq_rootedCutExpectation n pre tail ha q₀ _
    (hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n) _ tail (ha.suffix pre tail) 0)

theorem physicalRootLevelB_eq_stepPairDisorder (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (j : ℕ) (hj : j ≤ steps.length) :
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀
      (fun σ τ => (orderedOverlap n σ τ)^2) steps j =
      stepPairDisorder (uniformWeight n) (finiteFeature n) q₀ (steps.take j) (steps.drop j)
        (fun σ τ => (orderedOverlap n σ τ)^2) 0 := by
  have ho : OrderedSteps 0 (steps.take j ++ steps.drop j) := by
    simpa only [List.take_append_drop] using ha
  rw [stepPairDisorder, stepPairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n)
    _ _ _ (ho.suffix (steps.take j) (steps.drop j))]
  simp only [List.take_append_drop, List.length_take, min_eq_left hj, rootLevelPairMean]

theorem physicalSampledB_weighted_integral_le_cutBounds (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (weights bounds : ℕ → ℝ)
    (hweights : ∀ j ≤ as.length, 0 ≤ weights j)
    (hcuts : ∀ j ≤ as.length, 0 < weights j →
      let steps := sampleClockSteps (completedPathClock (n + 1) b h) 0 as
      stepPairDisorder (uniformWeight (n + 1)) (finiteFeature (n + 1))
        (completedPathClock (n + 1) b h 0) (steps.take j) (steps.drop j)
        (fun σ τ => (orderedOverlap (n + 1) σ τ)^2) 0 ≤ bounds j) :
    (∫ u in 0..1, massStepFunction as weights u * physicalSampledB n b h as ha u) ≤
      massStepSum as 0 (fun j => weights j * bounds j) := by
  rw [physicalSampledB_weighted_integral_eq_massStepSum]
  apply massStepSum_mono as ha
  intro j hj
  by_cases hz : weights j = 0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_left _ (hweights j hj)
    rw [physicalRootLevelB_eq_stepPairDisorder (n + 1) _ (sampleClockSteps_ordered _ as ha)
      _ j (by simpa only [sampleClockSteps_length] using hj)]
    exact hcuts j hj (lt_of_le_of_ne (hweights j hj) (Ne.symm hz))

end
end OAI.SKFluctuations.LaplaceWindowFormalization
