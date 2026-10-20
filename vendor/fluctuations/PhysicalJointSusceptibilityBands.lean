module

public import PhysicalSusceptibilityBands

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalFilledSourceHessian_clock_continuous (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m : ℝ) (x : FeatureIndex n → ℝ) (i j : Fin n) :
    Continuous (fun p : ℝ × (Fin (d + 1) → ℝ) =>
      physicalFilledSourceHessian n d L steps m p.1 0 x p.2 i j) := by
  let J := physicalSpinFeatureJet n d i L steps ha x
  have hG := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ j) steps ha 0).affine_zero L x
  have hH := (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1))
    steps ha 0).affine_zero L x
  simpa only [physicalFilledSourceHessian, actualSpinMean, physicalSourceHessian_eq_response,
    J, physicalSpinFeatureJet, gaussianFeatureJet_F, gaussianFeatureJet_A, sub_zero] using
    clockGradient_continuous J.lipschitz hG J.smoothA hH m

theorem physicalFilledSourceHessian_clock_bounded (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m : ℝ) (x : FeatureIndex n → ℝ) (i j : Fin n) :
    AbsBounded (fun p : ℝ × (Fin (d + 1) → ℝ) =>
      physicalFilledSourceHessian n d L steps m p.1 0 x p.2 i j) := by
  let J := physicalSpinFeatureJet n d i L steps ha x
  have hG := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ j) steps ha 0).affine_zero L x
  have hH := (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1))
    steps ha 0).affine_zero L x
  simpa only [physicalFilledSourceHessian, actualSpinMean, physicalSourceHessian_eq_response,
    J, physicalSpinFeatureJet, gaussianFeatureJet_F, gaussianFeatureJet_A, sub_zero] using
    clockGradient_absBounded J.lipschitz hG J.smoothA hH m

theorem physicalFilledSourceTraceExpectation_continuous (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) (x : FeatureIndex n → ℝ) :
    Continuous (fun t => physicalFilledSourceTraceExpectation n d L steps ha hm T t x) := by
  apply continuous_finsetSum
  intro i _
  let V := (physicalSpinFeatureJet n d i L steps ha x).family hm
  let A (r : ℝ) (y : Fin (d + 1) → ℝ) :=
    ∑ j, (physicalFilledSourceHessian n d L steps m r 0 x y i j) ^ 2
  have hcA : Continuous (fun p : ℝ × (Fin (d + 1) → ℝ) => A p.1 p.2) := by
    apply continuous_finsetSum
    intro j _
    exact (physicalFilledSourceHessian_clock_continuous n d L steps ha m x i j).pow 2
  have hbA : AbsBounded (fun p : ℝ × (Fin (d + 1) → ℝ) => A p.1 p.2) := by
    apply AbsBounded.sum
    intro j
    simpa only [pow_two] using
      (physicalFilledSourceHessian_clock_bounded n d L steps ha m x i j).mul
        (physicalFilledSourceHessian_clock_bounded n d L steps ha m x i j)
  obtain ⟨K, _, hK⟩ := hbA
  have hmap : Continuous (fun t : ℝ => (t, T - t)) :=
    continuous_id.prodMk (continuous_const.sub continuous_id)
  have hc := (dynamic_clockTest_continuous V.lipschitz V.continuousF hcA
    (fun r y => hK (r, y)) m 0).comp hmap
  convert hc using 1
  ext t
  simp only [Function.comp_apply, V, A, HeatJet.family,
    physicalFilledSourceHessian, sub_zero]

theorem physicalJointGaussianDriver_fieldTrace_band_le (n d : ℕ) (hn : 0 < n)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (c : ℝ≥0) (hc : 0 < c) (hfield : ∀ j, q (Sum.inl j) = c)
    (steps : List (GaussianStep (FeatureIndex n))) {a m T l r M : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ T)
    (x : FeatureIndex n → ℝ)
    (hmean : physicalFilledOverlap n d (physicalJointGaussianDriver n d e q)
      steps ha hm T r x ≤ M) :
    (∫ t in l..r, physicalFilledSourceTraceExpectation n d
      (physicalJointGaussianDriver n d e q) steps ha hm T t x) ≤ M / ((n : ℝ) * c) := by
  have henergy := physicalFilledOverlap_subinterval_eq_integral_energy n d
    (physicalJointGaussianDriver n d e q) steps ha hm hl hlr hr x
  have h0 := physicalFilledOverlap_nonneg n d
    (physicalJointGaussianDriver n d e q) steps ha hm T l x
  apply trace_integral_le_from_energy hlr
    (mul_pos (by exact_mod_cast hn) (by exact_mod_cast hc))
    ((physicalFilledOverlapEnergy_continuous n d _ steps ha hm T x).intervalIntegrable l r)
    ((physicalFilledSourceTraceExpectation_continuous n d _ steps ha hm T x).intervalIntegrable l r)
  · intro t _
    exact physicalJointGaussianDriver_energy_ge_fieldClockTrace n d hn e q c hfield
      steps ha hm T t x
  · linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
