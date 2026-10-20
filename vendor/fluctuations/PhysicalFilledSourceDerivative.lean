module

public import PhysicalOverlapClockDerivative

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalFilledSpinMean (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) (m τ : ℝ)
    (x : FeatureIndex n → ℝ) (i : Fin n) : ℝ :=
  linearClockTest L m (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps)
    (fun y => actualSpinMean n steps y i) τ x

theorem physicalFilledSpinMean_hasDerivAt_source (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m T t : ℝ) (x : FeatureIndex n → ℝ)
    (i j : Fin n) (s : ℝ) :
    HasDerivAt (fun r => physicalFilledSpinMean n d L steps m (T - t)
      (x + r • physicalNormalizedSourceMap n (Pi.single j 1)) i)
      (physicalFilledSourceHessian n d L steps m T t
        (x + s • physicalNormalizedSourceMap n (Pi.single j 1)) 0 i j) s := by
  let F := gaussianHierarchy (uniformWeight n) (finiteFeature n) steps
  let G := fun y => actualSpinMean n steps y j
  let A := fun y => actualSpinMean n steps y i
  let H := fun y => hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
    (physicalNormalizedSourceMap n) steps y i j
  let v := physicalNormalizedSourceMap n (Pi.single j 1)
  obtain ⟨K, hFK⟩ := (gaussianHierarchy_regular (uniformWeight_pos n)
    (finiteFeature n) steps ha 0).1
  have hF : Continuous F := hFK.continuous
  have hG : BddSmooth 0 G := gaussianHierarchyMean_smooth (uniformWeight_pos n)
    (finiteFeature n) (fun σ => normalizedSpin n σ j) steps ha 0
  have hA : BddSmooth 0 A := gaussianHierarchyMean_smooth (uniformWeight_pos n)
    (finiteFeature n) (fun σ => normalizedSpin n σ i) steps ha 0
  have hH : BddSmooth 0 H := by
    simpa only [H, physicalSourceHessian_eq_response] using
      gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
        (fun σ => normalizedSpin n σ i) v steps ha 0
  obtain ⟨C, hC, hbC⟩ := hG.bound
  obtain ⟨B, hB, hbB⟩ := hA.bound
  obtain ⟨D, hD, hbD⟩ := hH.bound
  have hdF : ∀ (y : FeatureIndex n → ℝ) (r : ℝ),
      HasDerivAt (fun q : ℝ => F (y + q • v)) (G (y + r • v)) r := by
    intro y r
    simpa only [F, G, v, actualSpinMean, physicalNormalizedSourceMap_feature] using
      gaussianHierarchy_hasDerivAt (uniformWeight_pos n) (finiteFeature n) steps ha y v r
  have hdA : ∀ (y : FeatureIndex n → ℝ) (r : ℝ),
      HasDerivAt (fun q : ℝ => A (y + q • v)) (H (y + r • v)) r := by
    intro y r
    simpa only [A, H, actualSpinMean, physicalSourceHessian_eq_response] using
      gaussianHierarchyMean_hasDerivAt (uniformWeight_pos n) (finiteFeature n)
        (fun σ => normalizedSpin n σ i) steps ha y v r
  have hi : ∀ y, Integrable (fun z => Real.exp (m * F (y + z)))
      (linearGaussian L (Real.toNNReal (T - t))) :=
    fun y => (exponentialIncrement_linearGaussian L (Real.toNNReal (T - t))).integrable_shift hFK m y
  have hd := hasDerivAt_shiftedMean hC (add_nonneg hB hD) hF hG.continuous hA.continuous
    hH.continuous hdF hdA hbC (fun y => (hbB y).trans (by linarith))
    (fun y => (hbD y).trans (by linarith)) hi x s
  apply hd.congr_deriv
  change linearClockTest L m F H (T - t) (x + s • v) + m *
    (linearClockTest L m F (fun y => A y * G y) (T - t) (x + s • v) -
      linearClockTest L m F A (T - t) (x + s • v) *
      linearClockTest L m F G (T - t) (x + s • v)) = _
  rw [linearClockTest_eq L hF hH.continuous,
    linearClockTest_eq L hF (A := fun y => A y * G y) (hA.continuous.mul hG.continuous),
    linearClockTest_eq L hF hA.continuous, linearClockTest_eq L hF hG.continuous]
  rfl

theorem clockTest_affine_shift {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) {F A : (ι → ℝ) → ℝ}
    (hF : Continuous F) (hA : Continuous A) (m τ : ℝ) (x : ι → ℝ) (z : κ → ℝ) :
    clockTest m (fun y => F (x + L y)) (fun y => A (x + L y)) τ z =
      linearClockTest L m F A τ (x + L z) := by
  rw [linearClockTest_eq L hF hA]
  simp only [clockTest, shiftedMean, tiltedMean, zero_add, map_add, add_assoc]

theorem scaleDriver_clock_gaussian {ι : Type*} [Fintype ι]
    (q : ι → ℝ≥0) (τ : ℝ≥0) :
    MeasurePreserving (scaleDriver q) (Measure.pi fun _ : ι => gaussianReal 0 τ)
      (Measure.pi fun i => gaussianReal 0 (τ * q i)) := by
  apply measurePreserving_pi (fun _ => gaussianReal 0 τ) (fun i => gaussianReal 0 (τ * q i))
  intro i
  change MeasurePreserving (fun z : ℝ => Real.sqrt (q i : ℝ) * z) _ _
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.eq
  change Real.sqrt (q i : ℝ) ^ 2 * (τ : ℝ) = (τ : ℝ) * (q i : ℝ)
  rw [Real.sq_sqrt (q i).coe_nonneg, mul_comm]

theorem physicalJointGaussianDriver_linearGaussian (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0) (τ : ℝ≥0) :
    linearGaussian (physicalJointGaussianDriver n d e q) τ =
      Measure.pi (fun i => gaussianReal 0 (τ * q i)) := by
  have hcoord := coordinateEquiv_measPres e (fun _ => τ)
  have hp := (scaleDriver_clock_gaussian q τ).comp hcoord
  exact hp.map_eq

theorem physicalFilledSourceHessian_eq_linearGradient (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m T t : ℝ) (x : FeatureIndex n → ℝ)
    (z : Fin (d + 1) → ℝ) (i j : Fin n) :
    physicalFilledSourceHessian n d L steps m T t x z i j =
      linearClockTest L m (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps)
        (fun y => hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
          (physicalNormalizedSourceMap n) steps y i j) (T - t) (x + L z) + m *
      (linearClockTest L m (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps)
          (fun y => actualSpinMean n steps y i * actualSpinMean n steps y j) (T - t) (x + L z) -
        linearClockTest L m (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps)
          (fun y => actualSpinMean n steps y i) (T - t) (x + L z) *
        linearClockTest L m (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps)
          (fun y => actualSpinMean n steps y j) (T - t) (x + L z)) := by
  have hF := gaussianHierarchy_continuous (uniformWeight_pos n) (finiteFeature n) steps ha
  have hA := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) steps ha 0).continuous
  have hG := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ j) steps ha 0).continuous
  have hH : Continuous (fun y => hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps y i j) := by
    simpa only [physicalSourceHessian_eq_response] using
      (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
        (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1))
        steps ha 0).continuous
  unfold physicalFilledSourceHessian clockGradient
  rw [clockTest_affine_shift L hF hH,
    clockTest_affine_shift L hF (A := fun y => actualSpinMean n steps y i * actualSpinMean n steps y j)
      (hA.mul hG),
    clockTest_affine_shift L hF (A := fun y => actualSpinMean n steps y i) hA,
    clockTest_affine_shift L hF (A := fun y => actualSpinMean n steps y j) hG]

theorem physicalFilledSourceHessian_eq_hierarchy (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m T t : ℝ) (x : FeatureIndex n → ℝ)
    (z : Fin (d + 1) → ℝ) :
    physicalFilledSourceHessian n d (physicalJointGaussianDriver n d e q) steps m T t x z =
      hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
        (physicalNormalizedSourceMap n)
        ((m, fun k => Real.toNNReal (T - t) * q k) :: steps)
        (x + physicalJointGaussianDriver n d e q z) := by
  ext i j
  rw [physicalFilledSourceHessian_eq_linearGradient n d _ steps ha,
    physicalSourceHessian_eq_response]
  simp only [linearClockTest, physicalJointGaussianDriver_linearGaussian,
    physicalSourceHessian_eq_response, gaussianHierarchyResponse, gaussianHierarchyMean,
    physicalNormalizedSourceMap_feature, actualSpinMean]

def physicalFilledSourceCovariance (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (m T t : ℝ)
    (x : FeatureIndex n → ℝ) (z : Fin (d + 1) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  hierarchySourceCovarianceMatrix (uniformWeight n) (finiteFeature n)
    (physicalNormalizedSourceMap n)
    ((m, fun k => Real.toNNReal (T - t) * q k) :: steps)
    (x + physicalJointGaussianDriver n d e q z)

theorem physicalFilledSourceCovarianceHessian_trace (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a u : ℝ}
    (ha : OrderedSteps a steps) (hu : 0 < u) (m T t : ℝ)
    (hord : OrderedSteps u ((m, fun k => Real.toNNReal (T - t) * q k) :: steps))
    (x : FeatureIndex n → ℝ) (z : Fin (d + 1) → ℝ) :
    let C := physicalFilledSourceCovariance n d e q steps m T t x z
    let H := physicalFilledSourceHessian n d (physicalJointGaussianDriver n d e q) steps m T t x z
    (H * C).trace ≤ (∑ i, ∑ j, (H i j) ^ 2) / u ∧
      (∑ i, ∑ j, (C i j) ^ 2) ≤ (∑ i, ∑ j, (H i j) ^ 2) / u ^ 2 := by
  dsimp only
  rw [physicalFilledSourceHessian_eq_hierarchy n d e q steps ha]
  exact physicalSourceCovarianceHessian_trace n _ hord hu _

end
end OAI.SKFluctuations.LaplaceWindowFormalization
