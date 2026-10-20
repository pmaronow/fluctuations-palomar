module

public import PhysicalCapIndexedTrace
public import PhysicalSourceTraceBounds

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalFilledSourceHessian_entry_squares_le_one (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ)
    (z : Fin (d + 1) → ℝ) :
    (∑ i, ∑ j, (physicalFilledSourceHessian n d (physicalJointGaussianDriver n d e q)
      steps m T t x z i j) ^ 2) ≤ 1 := by
  rw [physicalFilledSourceHessian_eq_hierarchy n d e q steps ha]
  exact physicalSourceHessianMatrix_entry_squares_le_one n _
    (show OrderedSteps 0 ((m, fun k => Real.toNNReal (T - t) * q k) :: steps) from
      ⟨by norm_num, hm.le, hm, ha⟩) _

theorem physicalFilledSourceTraceExpectation_eq_clockTest (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    physicalFilledSourceTraceExpectation n d L steps ha hm T t x =
      clockTest m (clockContinuation m (fun z => gaussianHierarchy (uniformWeight n)
        (finiteFeature n) steps (x + L z)) (T - t))
        (fun z => ∑ i, ∑ j, (physicalFilledSourceHessian n d L steps m T t x z i j) ^ 2) t 0 := by
  obtain ⟨C, hBase⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) steps ha
  have hFl := hBase.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)
  have hF := lipschitzWith_shiftedContinuation hFl hm (fun z =>
    (exponentialIncrement_gaussian (fun _ => Real.toNNReal (T - t))).integrable_shift hFl m z)
  have hrow : ∀ i : Fin n, BddSmooth 0
      (fun z => ∑ j, (physicalFilledSourceHessian n d L steps m T t x z i j) ^ 2) := by
    intro i
    apply BddSmooth.sum Finset.univ
    intro j _
    simpa only [pow_two] using (physicalFilledSourceHessian_smooth n d L steps ha m T t x i j).mul
      (physicalFilledSourceHessian_smooth n d L steps ha m T t x i j)
  symm
  convert clockTest_sum hF hrow m t (0 : Fin (d + 1) → ℝ) using 1 <;> rfl

theorem physicalFilledSourceTraceExpectation_le_one (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    physicalFilledSourceTraceExpectation n d (physicalJointGaussianDriver n d e q)
      steps ha hm T t x ≤ 1 := by
  let L := physicalJointGaussianDriver n d e q
  obtain ⟨C, hBase⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) steps ha
  have hFl := hBase.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)
  have hF := lipschitzWith_shiftedContinuation hFl hm (fun z =>
    (exponentialIncrement_gaussian (fun _ => Real.toNNReal (T - t))).integrable_shift hFl m z)
  have hA : BddSmooth 0 (fun z => ∑ i, ∑ j,
      (physicalFilledSourceHessian n d L steps m T t x z i j) ^ 2) := by
    apply BddSmooth.sum Finset.univ
    intro i _
    apply BddSmooth.sum Finset.univ
    intro j _
    simpa only [pow_two] using (physicalFilledSourceHessian_smooth n d L steps ha m T t x i j).mul
      (physicalFilledSourceHessian_smooth n d L steps ha m T t x i j)
  rw [physicalFilledSourceTraceExpectation_eq_clockTest n d L steps ha hm]
  have h := clockTest_mono hF hA (BddSmooth.const 0 (1 : ℝ))
    (physicalFilledSourceHessian_entry_squares_le_one n d e q steps ha hm T t x) m t 0
  rwa [clockTest_const hF] at h

theorem physicalFilledSourceTrace_integral_le_one (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (x : FeatureIndex n → ℝ) :
    (∫ t in 0..1, physicalFilledSourceTraceExpectation n d
      (physicalJointGaussianDriver n d e q) steps ha hm 1 t x) ≤ 1 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((physicalFilledSourceTraceExpectation_continuous n d _ steps ha hm 1 x).intervalIntegrable 0 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1)
    (fun t _ => physicalFilledSourceTraceExpectation_le_one n d e q steps ha hm 1 t x)
  simpa using h

theorem physicalFiniteCapIndexedTrace_nonneg (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (x : FeatureIndex (n + 1) → ℝ) :
    0 ≤ physicalFiniteCapIndexedTrace n d e durations pre tail ha x := by
  induction pre generalizing a durations x with
  | nil => cases durations <;> exact le_rfl
  | cons st pre ih =>
    cases durations with
    | nil => exact le_rfl
    | cons w durations =>
      rcases st with ⟨m, q⟩
      apply add_nonneg
      · apply mul_nonneg w.coe_nonneg
        apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        intro t _
        exact physicalFilledSourceTraceExpectation_nonneg (n + 1) d _ (pre ++ tail)
          ha.2.2.2 ha.2.2.1 1 t x
      · exact shiftedMean_nonneg (ih durations ha.2.2.2)
          (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
            (pre ++ tail) ha.2.2.2 m q x)

theorem physicalFiniteCapIndexedTrace_le_durationSum (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (x : FeatureIndex (n + 1) → ℝ) :
    physicalFiniteCapIndexedTrace n d e durations pre tail ha x ≤ durations.sum := by
  induction pre generalizing a durations x with
  | nil => cases durations <;> exact NNReal.coe_nonneg _
  | cons st pre ih =>
    cases durations with
    | nil => exact le_rfl
    | cons w durations =>
      rcases st with ⟨m, q⟩
      simp only [physicalFiniteCapIndexedTrace, List.sum_cons, NNReal.coe_add]
      apply add_le_add
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (physicalFilledSourceTrace_integral_le_one (n + 1) d e q (pre ++ tail)
            ha.2.2.2 ha.2.2.1 x) w.coe_nonneg
      · have h := shiftedMean_mono
          (physicalFiniteCapIndexedTrace_smooth n d e durations pre tail ha.2.2.2)
          (BddSmooth.const 0 (durations.sum : ℝ)) (ih durations ha.2.2.2)
          (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
            (pre ++ tail) ha.2.2.2 m q x)
        rwa [shiftedMean_const _ (gaussianHierarchy_integrable (uniformWeight_pos (n + 1))
          (finiteFeature (n + 1)) (pre ++ tail) ha.2.2.2 m q x)] at h

end
end OAI.SKFluctuations.LaplaceWindowFormalization
