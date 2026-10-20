module

public import PhysicalFilledHessianSplitting
public import PhysicalFilledTraceBound

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalFilledOverlap_monotoneOn (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) (x : FeatureIndex n → ℝ) :
    MonotoneOn (fun t => physicalFilledOverlap n d L steps ha hm T t x) (Icc (0:ℝ) T) := by
  intro l hl r hr hlr
  have heq := physicalFilledOverlap_subinterval_eq_integral_energy n d L steps ha hm hl.1 hlr hr.2 x
  have hnonneg : 0 ≤ ∫ t in l..r, physicalFilledOverlapEnergy n d L steps ha hm T t x := by
    apply intervalIntegral.integral_nonneg hlr
    intro t _
    exact physicalFilledOverlapEnergy_nonneg n d L steps ha hm T t x
  linarith

theorem physicalBoundaryTrace_le_filledTrace_point (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m t : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (ht : t ∈ Icc (0:ℝ) 1)
    (x : FeatureIndex n → ℝ) :
    (∑ i, ∑ j, (hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) ((m,q)::steps) x i j)^2) ≤
      2*physicalFilledSourceTraceExpectation n d (physicalJointGaussianDriver n d e q)
        steps ha hm 1 t x +
      2*m^2*(physicalFilledOverlap n d (physicalJointGaussianDriver n d e q)
        steps ha hm 1 t x - physicalFilledOverlap n d (physicalJointGaussianDriver n d e q)
        steps ha hm 1 0 x) := by
  let L := physicalJointGaussianDriver n d e q
  let μ := physicalFilledDriverLaw n d L steps m 1 t x
  let X (i : Fin n) (z : Fin (d+1) → ℝ) :=
    physicalFilledDriverSpinMean n d L steps m 1 t x z i
  let H (z : Fin (d+1) → ℝ) := physicalFilledSourceHessian n d L steps m 1 t x z
  let C := physicalFilledDriverMeanCovariance n d L steps m 1 t x
  let K := physicalFilledSourceHessian n d L steps m 1 0 x 0
  let : IsProbabilityMeasure μ := physicalFilledDriverLaw_probability n d L steps ha hm 1 t x
  have hX (i : Fin n) : MemLp (X i) 2 μ :=
    physicalFilledDriverSpinMean_memLp n d L steps ha hm 1 t x i 2
  have hH (i j : Fin n) : MemLp (fun z => H z i j) 2 μ :=
    physicalFilledSourceHessian_memLp n d L steps ha hm 1 t x i j 2
  have hCov : C = probabilityVectorCovariance μ X :=
    physicalFilledDriverMeanCovariance_eq_probabilityCovariance n d L steps ha hm ht x
  have hC : C.PosSemidef := by
    rw [hCov]
    exact probabilityVectorCovariance_posSemidef μ X hX
  have htr : C.trace ≤ 1 := by
    rw [hCov]
    apply probabilityVectorCovariance_trace_le_one μ X hX
    exact Eventually.of_forall (physicalFilledDriverSpinMean_square_sum_le_one n d e q steps ha hm 1 t x)
  have hsplit (i j : Fin n) : K i j = (∫ z, H z i j ∂μ)+m*C i j := by
    rw [physicalFilledDriverLaw_integral_eq_clockTest n d L steps ha hm 1 t x]
    exact physicalFilledSourceHessian_split n d L steps ha hm ht x i j
  have h := hessian_projection_square_le μ H hH hC htr hsplit
  have hstart : K = hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) ((m,q)::steps) x := by
    simpa only [Real.toNNReal_one, one_mul] using
      physicalFilledSourceHessian_start_eq_hierarchy n d e q steps ha m 1 x
  rw [hstart] at h
  have hint : (∫ z, ∑ i, ∑ j, (H z i j)^2 ∂μ) =
      physicalFilledSourceTraceExpectation n d L steps ha hm 1 t x := by
    rw [physicalFilledDriverLaw_integral_eq_clockTest n d L steps ha hm 1 t x]
    exact (physicalFilledSourceTraceExpectation_eq_clockTest n d L steps ha hm 1 t x).symm
  rw [hint] at h
  simpa only [C, L, physicalFilledDriverMeanCovariance_trace n d L steps ha hm 1 t x] using h

theorem physicalBoundaryTrace_le_filledTrace_and_energy (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (x : FeatureIndex n → ℝ) :
    (∑ i, ∑ j, (hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) ((m,q)::steps) x i j)^2) ≤
      2*(∫ t in 0..1, physicalFilledSourceTraceExpectation n d
        (physicalJointGaussianDriver n d e q) steps ha hm 1 t x) +
      2*m^2*(∫ t in 0..1, physicalFilledOverlapEnergy n d
        (physicalJointGaussianDriver n d e q) steps ha hm 1 t x) := by
  let L := physicalJointGaussianDriver n d e q
  let K := ∑ i, ∑ j, (hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) ((m,q)::steps) x i j)^2
  let Δ := physicalFilledOverlap n d L steps ha hm 1 1 x -
    physicalFilledOverlap n d L steps ha hm 1 0 x
  have hpoint (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      K ≤ 2*physicalFilledSourceTraceExpectation n d L steps ha hm 1 t x+2*m^2*Δ := by
    have h := physicalBoundaryTrace_le_filledTrace_point n d e q steps ha hm ht x
    have hmono := physicalFilledOverlap_monotoneOn n d L steps ha hm 1 x ht
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) ht.2
    change K ≤ _ at h
    change _ ≤ 2*physicalFilledSourceTraceExpectation n d L steps ha hm 1 t x+2*m^2*Δ
    nlinarith [sq_nonneg m]
  have htrace : IntervalIntegrable (fun t => physicalFilledSourceTraceExpectation n d L steps ha hm 1 t x) volume 0 1 :=
    (physicalFilledSourceTraceExpectation_continuous n d L steps ha hm 1 x).intervalIntegrable 0 1
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K) volume 0 1)
    ((htrace.const_mul 2).add (intervalIntegrable_const)) hpoint
  rw [intervalIntegral.integral_add (htrace.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul] at hh
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hh
  have heq := physicalFilledOverlap_increment_eq_integral_energy n d L steps ha hm
    (by norm_num : (0:ℝ) ≤ 1) x
  change Δ = _ at heq
  rw [heq] at hh
  exact hh

end OAI.SKFluctuations.LaplaceWindowFormalization
