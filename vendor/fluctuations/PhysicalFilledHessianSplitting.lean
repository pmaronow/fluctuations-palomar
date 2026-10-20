module

public import ClockGradientSplitting
public import PhysicalCapEnergyConcatenation
public import PhysicalSourceTraceBounds
public import WallBoundaryTraceAlgebra

@[expose] public section
set_option maxHeartbeats 800000

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def physicalFilledDriverPotential (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) (m T t : ℝ)
    (x : FeatureIndex n → ℝ) : (Fin (d+1) → ℝ) → ℝ :=
  clockContinuation m
    (fun z => gaussianHierarchy (uniformWeight n) (finiteFeature n) steps (x+L z)) (T-t)

def physicalFilledDriverSpinMean (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) (m T t : ℝ)
    (x : FeatureIndex n → ℝ) (z : Fin (d+1) → ℝ) (i : Fin n) : ℝ :=
  clockTest m
    (fun y => gaussianHierarchy (uniformWeight n) (finiteFeature n) steps (x+L y))
    (fun y => actualSpinMean n steps (x+L y) i) (T-t) z

def physicalFilledDriverMeanCovariance (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) (m T t : ℝ)
    (x : FeatureIndex n → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  clockTest m (physicalFilledDriverPotential n d L steps m T t x)
    (fun z => physicalFilledDriverSpinMean n d L steps m T t x z i *
      physicalFilledDriverSpinMean n d L steps m T t x z j) t 0 -
    physicalFilledDriverSpinMean n d L steps m T 0 x 0 i *
      physicalFilledDriverSpinMean n d L steps m T 0 x 0 j

theorem physicalFilledSourceHessian_split (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m T t : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (ht : t ∈ Icc (0:ℝ) T)
    (x : FeatureIndex n → ℝ) (i j : Fin n) :
    physicalFilledSourceHessian n d L steps m T 0 x 0 i j =
      clockTest m (physicalFilledDriverPotential n d L steps m T t x)
        (fun z => physicalFilledSourceHessian n d L steps m T t x z i j) t 0 +
      m * physicalFilledDriverMeanCovariance n d L steps m T t x i j := by
  let J := physicalSpinFeatureJet n d i L steps ha x
  have hG := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ j) steps ha 0).affine_zero L x
  have hH := (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1))
    steps ha 0).affine_zero L x
  have he := clockGradient_split J.regular hG J.smoothA hH hm ht.1
    (sub_nonneg.mpr ht.2) (0 : Fin (d+1) → ℝ)
  have htime : t+(T-t)=T := by ring
  simpa only [htime, physicalFilledSourceHessian, physicalFilledDriverPotential,
    physicalFilledDriverSpinMean, physicalFilledDriverMeanCovariance,
    sub_zero, actualSpinMean, physicalSourceHessian_eq_response, J,
    physicalSpinFeatureJet, gaussianFeatureJet_F, gaussianFeatureJet_A] using he

theorem physicalFilledDriverSpinMean_tower (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m T t : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (ht : t ∈ Icc (0:ℝ) T)
    (x : FeatureIndex n → ℝ) (i : Fin n) :
    clockTest m (physicalFilledDriverPotential n d L steps m T t x)
      (fun z => physicalFilledDriverSpinMean n d L steps m T t x z i) t 0 =
      physicalFilledDriverSpinMean n d L steps m T 0 x 0 i := by
  let J := physicalSpinFeatureJet n d i L steps ha x
  have he := clockTest_add J.lipschitz J.smoothA hm.ne' ht.1
    (sub_nonneg.mpr ht.2) (0 : Fin (d+1) → ℝ)
  have htime : t+(T-t)=T := by ring
  simpa only [htime, physicalFilledDriverPotential, physicalFilledDriverSpinMean,
    sub_zero, actualSpinMean, J, physicalSpinFeatureJet, gaussianFeatureJet_F,
    gaussianFeatureJet_A] using he

theorem physicalFilledDriverMeanCovariance_trace (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex n → ℝ) :
    (physicalFilledDriverMeanCovariance n d L steps m T t x).trace =
      physicalFilledOverlap n d L steps ha hm T t x -
      physicalFilledOverlap n d L steps ha hm T 0 x := by
  unfold Matrix.trace Matrix.diag physicalFilledDriverMeanCovariance physicalFilledOverlap
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [HeatJet.filledSquare_zero]
  simp only [HeatJet.filledSquare, HeatJet.evolve, HeatJet.square,
    physicalFilledDriverPotential, physicalFilledDriverSpinMean,
    physicalSpinFeatureJet, gaussianFeatureJet_F, gaussianFeatureJet_A, pow_two, sub_zero,
    actualSpinMean]

theorem physicalFilledSourceHessian_start_eq_hierarchy (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (m T : ℝ) (x : FeatureIndex n → ℝ) :
    physicalFilledSourceHessian n d (physicalJointGaussianDriver n d e q)
      steps m T 0 x 0 =
      hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
        (physicalNormalizedSourceMap n) ((m,fun k => Real.toNNReal T*q k)::steps) x := by
  simpa only [sub_zero, map_zero, add_zero] using
    physicalFilledSourceHessian_eq_hierarchy n d e q steps ha m T 0 x 0

theorem physicalFilledDriverSpinMean_eq_hierarchy (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (m T t : ℝ) (x : FeatureIndex n → ℝ) (z : Fin (d+1) → ℝ) (i : Fin n) :
    physicalFilledDriverSpinMean n d (physicalJointGaussianDriver n d e q)
      steps m T t x z i =
      actualSpinMean n ((m,fun k => Real.toNNReal (T-t)*q k)::steps)
        (x+physicalJointGaussianDriver n d e q z) i := by
  unfold physicalFilledDriverSpinMean
  rw [clockTest_affine_shift _
    (gaussianHierarchy_continuous (uniformWeight_pos n) (finiteFeature n) steps ha)
    (A := fun y => actualSpinMean n steps y i)
    (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) steps ha 0).continuous]
  simp only [linearClockTest, physicalJointGaussianDriver_linearGaussian]
  rfl

theorem physicalFilledDriverSpinMean_square_sum_le_one (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) {m : ℝ}
    (ha : OrderedSteps m steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex n → ℝ) (z : Fin (d+1) → ℝ) :
    (∑ i, (physicalFilledDriverSpinMean n d (physicalJointGaussianDriver n d e q)
      steps m T t x z i)^2) ≤ 1 := by
  simp_rw [physicalFilledDriverSpinMean_eq_hierarchy n d e q steps ha]
  have hord : OrderedSteps (0:ℝ) ((m,fun k => Real.toNNReal (T-t)*q k)::steps) :=
    ⟨le_rfl,hm.le,hm,ha⟩
  have h := actualSpinMean_norm_le n _ hord (x+physicalJointGaussianDriver n d e q z)
  have hs := (Real.sqrt_le_left zero_le_one).mp h
  norm_num at hs
  exact hs

def physicalFilledDriverLaw (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) (m T t : ℝ)
    (x : FeatureIndex n → ℝ) : Measure (Fin (d+1) → ℝ) :=
  tiltedLaw (Measure.pi fun _ => gaussianReal 0 (Real.toNNReal t)) m
    (physicalFilledDriverPotential n d L steps m T t x)

theorem physicalFilledDriverPotential_lipschitz (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    ∃ C : ℝ≥0, LipschitzWith C (physicalFilledDriverPotential n d L steps m T t x) := by
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) steps ha
  have hshift : LipschitzWith ‖L‖₊ (fun z => x+L z) := by
    simpa only [zero_add] using (LipschitzWith.const x).add L.lipschitzWith
  have hFa : LipschitzWith (C * ‖L‖₊)
      (fun z => gaussianHierarchy (uniformWeight n) (finiteFeature n) steps (x+L z)) :=
    hF.comp hshift
  have hi (y) := (exponentialIncrement_gaussian
    (fun _ : Fin (d+1) => Real.toNNReal (T-t))).integrable_shift hFa m y
  refine ⟨C * ‖L‖₊,?_⟩
  change LipschitzWith (C * ‖L‖₊) (shiftedContinuation
    (Measure.pi fun _ : Fin (d+1) => gaussianReal 0 (Real.toNNReal (T-t))) m
    (fun z => gaussianHierarchy (uniformWeight n) (finiteFeature n) steps (x+L z)))
  exact lipschitzWith_shiftedContinuation hFa hm hi

theorem physicalFilledDriverLaw_probability (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    IsProbabilityMeasure (physicalFilledDriverLaw n d L steps m T t x) := by
  obtain ⟨C,hC⟩ := physicalFilledDriverPotential_lipschitz n d L steps ha hm T t x
  apply tiltedLaw_isProbability
  simpa only [zero_add] using
    (exponentialIncrement_gaussian (fun _ : Fin (d+1) => Real.toNNReal t)).integrable_shift hC m 0

theorem physicalFilledDriverLaw_integral_eq_clockTest (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ)
    (A : (Fin (d+1) → ℝ) → ℝ) :
    (∫ z, A z ∂physicalFilledDriverLaw n d L steps m T t x) =
      clockTest m (physicalFilledDriverPotential n d L steps m T t x) A t 0 := by
  obtain ⟨C,hC⟩ := physicalFilledDriverPotential_lipschitz n d L steps ha hm T t x
  have hi : Integrable (fun z => Real.exp (m * physicalFilledDriverPotential n d L steps m T t x z))
      (Measure.pi fun _ : Fin (d+1) => gaussianReal 0 (Real.toNNReal t)) := by
    simpa only [zero_add] using
      (exponentialIncrement_gaussian (fun _ : Fin (d+1) => Real.toNNReal t)).integrable_shift hC m 0
  have h := integral_tiltedLaw (A := A) hC.continuous.measurable hi
  simpa only [physicalFilledDriverLaw,clockTest,shiftedMean,zero_add] using h

theorem physicalFilledDriverSpinMean_memLp (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ)
    (i : Fin n) (p : ℝ≥0∞) :
    MemLp (fun z => physicalFilledDriverSpinMean n d L steps m T t x z i) p
      (physicalFilledDriverLaw n d L steps m T t x) := by
  let J := physicalSpinFeatureJet n d i L steps ha x
  have hi (y) := (exponentialIncrement_gaussian
    (fun _ : Fin (d+1) => Real.toNNReal (T-t))).integrable_shift J.lipschitz m y
  have hA : BddSmooth 0 (fun z => physicalFilledDriverSpinMean n d L steps m T t x z i) := by
    simpa only [physicalFilledDriverSpinMean,J,physicalSpinFeatureJet,
      gaussianFeatureJet_F,gaussianFeatureJet_A,actualSpinMean,clockTest]
      using J.smoothA.shiftedMean J.regular hi
  obtain ⟨C,_,hC⟩ := hA.bound
  have := physicalFilledDriverLaw_probability n d L steps ha hm T t x
  exact MemLp.of_bound hA.continuous.measurable.aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)

theorem physicalFilledSourceHessian_memLp (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ)
    (i j : Fin n) (p : ℝ≥0∞) :
    MemLp (fun z => physicalFilledSourceHessian n d L steps m T t x z i j) p
      (physicalFilledDriverLaw n d L steps m T t x) := by
  have hH := physicalFilledSourceHessian_smooth n d L steps ha m T t x i j
  obtain ⟨C,_,hC⟩ := hH.bound
  have := physicalFilledDriverLaw_probability n d L steps ha hm T t x
  exact MemLp.of_bound hH.continuous.measurable.aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)

theorem physicalFilledDriverMeanCovariance_eq_probabilityCovariance (n d : ℕ)
    (L : (Fin (d+1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m T t : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (ht : t ∈ Icc (0:ℝ) T)
    (x : FeatureIndex n → ℝ) :
    physicalFilledDriverMeanCovariance n d L steps m T t x =
      probabilityVectorCovariance (physicalFilledDriverLaw n d L steps m T t x)
        (fun i z => physicalFilledDriverSpinMean n d L steps m T t x z i) := by
  have := physicalFilledDriverLaw_probability n d L steps ha hm T t x
  ext i j
  rw [probabilityVectorCovariance_apply _ _
    (fun i => physicalFilledDriverSpinMean_memLp n d L steps ha hm T t x i 2)]
  simp_rw [physicalFilledDriverLaw_integral_eq_clockTest n d L steps ha hm T t x]
  rw [physicalFilledDriverSpinMean_tower n d L steps ha hm ht x i,
    physicalFilledDriverSpinMean_tower n d L steps ha hm ht x j]
  rfl

end OAI.SKFluctuations.LaplaceWindowFormalization
