module

public import PhysicalFilledSourceDerivative

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalSpinMeanSq (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (x : FeatureIndex n → ℝ) : ℝ := ∑ i, (actualSpinMean n steps x i) ^ 2

theorem physicalSpinMeanSq_smooth (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps) :
    BddSmooth 0 (physicalSpinMeanSq n steps) := by
  apply BddSmooth.sum Finset.univ
  intro i _
  simpa only [physicalSpinMeanSq, actualSpinMean, pow_two] using
    (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) steps ha 0).mul
      (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
        (fun σ => normalizedSpin n σ i) steps ha 0)

theorem physicalFilledOverlap_zero_eq_meanSq (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) (x : FeatureIndex n → ℝ) :
    physicalFilledOverlap n d (physicalJointGaussianDriver n d e q) steps ha hm T 0 x =
      physicalSpinMeanSq n ((m, fun k => Real.toNNReal T * q k) :: steps) x := by
  unfold physicalFilledOverlap physicalSpinMeanSq
  apply Finset.sum_congr rfl
  intro i _
  rw [HeatJet.filledSquare_zero]
  change (clockTest m
    (fun z => gaussianHierarchy (uniformWeight n) (finiteFeature n) steps
      (x + physicalJointGaussianDriver n d e q z))
    (fun z => actualSpinMean n steps (x + physicalJointGaussianDriver n d e q z) i) T 0) ^ 2 = _
  rw [← linearClockTest_eq _ (gaussianHierarchy_continuous (uniformWeight_pos n) _ steps ha)
    (A := fun y => actualSpinMean n steps y i)
    (gaussianHierarchyMean_smooth (uniformWeight_pos n) _
      (fun σ => normalizedSpin n σ i) steps ha 0).continuous]
  simp only [linearClockTest, physicalJointGaussianDriver_linearGaussian]
  rfl

theorem physicalFilledSpinSquare_terminal_eq_test (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ)
    (x : FeatureIndex n → ℝ) (i : Fin n) :
    (physicalSpinFeatureJet n d i (physicalJointGaussianDriver n d e q) steps ha x).filledSquare hm T T 0 =
      shiftedMean (Measure.pi fun k => gaussianReal 0 (Real.toNNReal T * q k)) m
        (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps)
        (fun y => (actualSpinMean n steps y i) ^ 2) x := by
  rw [HeatJet.filledSquare_terminal]
  change clockTest m
    (fun z => gaussianHierarchy (uniformWeight n) (finiteFeature n) steps
      (x + physicalJointGaussianDriver n d e q z))
    (fun z => (actualSpinMean n steps (x + physicalJointGaussianDriver n d e q z) i) ^ 2) T 0 = _
  rw [← linearClockTest_eq _ (gaussianHierarchy_continuous (uniformWeight_pos n) _ steps ha)
    (A := fun y => (actualSpinMean n steps y i) ^ 2)
    ((gaussianHierarchyMean_smooth (uniformWeight_pos n) _
      (fun σ => normalizedSpin n σ i) steps ha 0).continuous.pow 2)]
  simp only [linearClockTest, physicalJointGaussianDriver_linearGaussian]

theorem physicalFilledOverlap_terminal_eq_test (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) (x : FeatureIndex n → ℝ) :
    physicalFilledOverlap n d (physicalJointGaussianDriver n d e q) steps ha hm T T x =
      shiftedMean (Measure.pi fun k => gaussianReal 0 (Real.toNNReal T * q k)) m
        (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps) (physicalSpinMeanSq n steps) x := by
  unfold physicalFilledOverlap
  simp_rw [physicalFilledSpinSquare_terminal_eq_test]
  apply (shiftedMean_sum (fun i => ?_)
    (gaussianHierarchy_integrable (uniformWeight_pos n) _ steps ha m _ x)).symm
  simpa only [pow_two, actualSpinMean] using
    (gaussianHierarchyMean_smooth (uniformWeight_pos n) _
      (fun σ => normalizedSpin n σ i) steps ha 0).mul
      (gaussianHierarchyMean_smooth (uniformWeight_pos n) _
        (fun σ => normalizedSpin n σ i) steps ha 0)

theorem physicalFilledEnergy_integral_eq_increment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a m T : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hT : 0 ≤ T) (x : FeatureIndex n → ℝ) :
    (∫ t in 0..T, physicalFilledOverlapEnergy n d (physicalJointGaussianDriver n d e q)
      steps ha hm T t x) =
      shiftedMean (Measure.pi fun k => gaussianReal 0 (Real.toNNReal T * q k)) m
        (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps) (physicalSpinMeanSq n steps) x -
      physicalSpinMeanSq n ((m, fun k => Real.toNNReal T * q k) :: steps) x := by
  rw [← physicalFilledOverlap_increment_eq_integral_energy _ _ _ _ ha hm hT,
    physicalFilledOverlap_terminal_eq_test, physicalFilledOverlap_zero_eq_meanSq]

def physicalFiniteCapEnergy (n d : ℕ) (e : Fin (d + 1) ≃ FeatureIndex n) :
    (pre tail : List (GaussianStep (FeatureIndex n))) → {a : ℝ} →
      OrderedSteps a (pre ++ tail) → (FeatureIndex n → ℝ) → ℝ
  | [], _, _, _, _ => 0
  | (m, q) :: pre, tail, _, ha, x =>
      (∫ t in 0..1, physicalFilledOverlapEnergy n d (physicalJointGaussianDriver n d e q)
        (pre ++ tail) ha.2.2.2 ha.2.2.1 1 t x) +
      shiftedMean (Measure.pi fun k => gaussianReal 0 (q k)) m
        (gaussianHierarchy (uniformWeight n) (finiteFeature n) (pre ++ tail))
        (physicalFiniteCapEnergy n d e pre tail ha.2.2.2) x

theorem physicalFiniteCapEnergy_eq_increment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (x : FeatureIndex n → ℝ) :
    physicalFiniteCapEnergy n d e pre tail ha x =
      prefixTest pre (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
        (physicalSpinMeanSq n tail) x - physicalSpinMeanSq n (pre ++ tail) x := by
  induction pre generalizing a x with
  | nil => simp [physicalFiniteCapEnergy, prefixTest]
  | cons st pre ih =>
    rcases st with ⟨m, q⟩
    obtain ⟨b, hb⟩ := orderedSteps_append_right pre tail ha.2.2.2
    obtain ⟨C, hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) tail hb
    have hpos : ∀ st ∈ pre, 0 < st.1 := fun st hs =>
      ha.2.2.2.mem_pos st (List.mem_append_left tail hs)
    have hA := prefixTest_smooth0 hF (physicalSpinMeanSq_smooth n tail hb) pre hpos
    have hB := physicalSpinMeanSq_smooth n (pre ++ tail) ha.2.2.2
    simp only [physicalFiniteCapEnergy]
    rw [physicalFilledEnergy_integral_eq_increment n d e q (pre ++ tail) ha.2.2.2 ha.2.2.1
      (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [Real.toNNReal_one, one_mul]
    rw [funext (ih ha.2.2.2), shiftedMean_sub hA hB
      (gaussianHierarchy_integrable (uniformWeight_pos n) (finiteFeature n) (pre ++ tail)
        ha.2.2.2 m q x)]
    simp only [prefixTest, prefixContinuation_hierarchy, List.cons_append]
    ring

theorem physicalFiniteCapEnergy_smooth (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) :
    BddSmooth 0 (physicalFiniteCapEnergy n d e pre tail ha) := by
  rw [funext (physicalFiniteCapEnergy_eq_increment n d e pre tail ha)]
  obtain ⟨b, hb⟩ := orderedSteps_append_right pre tail ha
  obtain ⟨C, hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) tail hb
  exact (prefixTest_smooth0 hF (physicalSpinMeanSq_smooth n tail hb) pre
    (fun st hs => ha.mem_pos st (List.mem_append_left tail hs))).sub
      (physicalSpinMeanSq_smooth n (pre ++ tail) ha)

theorem physicalFiniteCapEnergy_eq_prefixLaw_increment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (x : FeatureIndex n → ℝ) :
    physicalFiniteCapEnergy n d e pre tail ha x =
      (∫ p, physicalSpinMeanSq n tail (forwardEnd pre.length (hierarchyIncrements pre) x p)
        ∂segmentLaw (uniformWeight n) (finiteFeature n) tail pre x) -
      physicalSpinMeanSq n (pre ++ tail) x := by
  obtain ⟨b, hb⟩ := orderedSteps_append_right pre tail ha
  rw [integral_segmentLaw_test (uniformWeight_pos n) (finiteFeature n)
    (physicalSpinMeanSq_smooth n tail hb) tail pre ha]
  exact physicalFiniteCapEnergy_eq_increment n d e pre tail ha x

theorem physicalSpinMeanSq_nonneg (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ) :
    0 ≤ physicalSpinMeanSq n steps x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem physicalFiniteCapEnergy_nonneg (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (x : FeatureIndex n → ℝ) :
    0 ≤ physicalFiniteCapEnergy n d e pre tail ha x := by
  induction pre generalizing a x with
  | nil => exact le_rfl
  | cons st pre ih =>
    rcases st with ⟨m, q⟩
    apply add_nonneg
    · apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      intro t _
      exact physicalFilledOverlapEnergy_nonneg n d _ (pre ++ tail) ha.2.2.2 ha.2.2.1 1 t x
    · exact shiftedMean_nonneg (ih ha.2.2.2)
        (gaussianHierarchy_integrable (uniformWeight_pos n) (finiteFeature n) (pre ++ tail)
          ha.2.2.2 m q x)

theorem physicalFiniteCapEnergy_rooted_eq_increment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q₀ : FeatureIndex n → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (x : FeatureIndex n → ℝ) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapEnergy n d e pre tail ha) x =
      zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
        (prefixTest pre (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
          (physicalSpinMeanSq n tail)) x -
      zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
        (physicalSpinMeanSq n (pre ++ tail)) x := by
  obtain ⟨b, hb⟩ := orderedSteps_append_right pre tail ha
  obtain ⟨C, hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) tail hb
  have hA := prefixTest_smooth0 hF (physicalSpinMeanSq_smooth n tail hb) pre
    (fun st hs => ha.mem_pos st (List.mem_append_left tail hs))
  have hB := physicalSpinMeanSq_smooth n (pre ++ tail) ha
  have hm : Measurable (fun z : FeatureIndex n → ℝ => x + z) := measurable_const.add measurable_id
  rw [funext (physicalFiniteCapEnergy_eq_increment n d e pre tail ha)]
  exact integral_sub (hA.integrable_comp_measurable hm) (hB.integrable_comp_measurable hm)

theorem physicalFiniteCapEnergy_rooted_le_endpoint (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q₀ : FeatureIndex n → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a M : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (x : FeatureIndex n → ℝ)
    (hmean : zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (prefixTest pre (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
        (physicalSpinMeanSq n tail)) x ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapEnergy n d e pre tail ha) x ≤ M := by
  rw [physicalFiniteCapEnergy_rooted_eq_increment]
  have h0 : 0 ≤ zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalSpinMeanSq n (pre ++ tail)) x :=
    integral_nonneg (fun z => physicalSpinMeanSq_nonneg n (pre ++ tail) (x + z))
  linarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
