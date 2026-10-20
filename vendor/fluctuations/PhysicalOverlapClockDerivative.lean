module

public import PhysicalSusceptibilityTrace

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalSpinFeatureJet (n d : ℕ) (i : Fin n)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex n → ℝ) : HeatJet d :=
  gaussianFeatureJet (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) L steps ha x

def physicalFilledOverlap (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) : ℝ :=
  ∑ i, (physicalSpinFeatureJet n d i L steps ha x).filledSquare hm T t 0

def physicalFilledOverlapEnergy (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) : ℝ :=
  ∑ i, (physicalSpinFeatureJet n d i L steps ha x).filledEnergy hm T t 0

theorem physicalFilledOverlap_hasDerivAt (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m T t : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (ht : t ∈ Ioo 0 T)
    (x : FeatureIndex n → ℝ) :
    HasDerivAt (fun s => physicalFilledOverlap n d L steps ha hm T s x)
      (physicalFilledOverlapEnergy n d L steps ha hm T t x) t := by
  convert HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (physicalSpinFeatureJet n d i L steps ha x).hasDerivAt_filledSquare hm ht 0) using 1
  · ext s
    simp [physicalFilledOverlap]
  · rfl

theorem physicalFilledOverlapEnergy_nonneg (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    0 ≤ physicalFilledOverlapEnergy n d L steps ha hm T t x :=
  Finset.sum_nonneg fun i _ =>
    (physicalSpinFeatureJet n d i L steps ha x).filledEnergy_nonneg hm T t 0

theorem physicalFilledOverlap_continuous (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) (x : FeatureIndex n → ℝ) :
    Continuous (fun t => physicalFilledOverlap n d L steps ha hm T t x) :=
  continuous_finsetSum _ fun i _ =>
    (physicalSpinFeatureJet n d i L steps ha x).continuous_filledSquare hm T 0

theorem physicalFilledOverlapEnergy_continuous (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) (x : FeatureIndex n → ℝ) :
    Continuous (fun t => physicalFilledOverlapEnergy n d L steps ha hm T t x) :=
  continuous_finsetSum _ fun i _ =>
    (physicalSpinFeatureJet n d i L steps ha x).continuous_filledEnergy hm T 0

theorem physicalFilledOverlap_increment_eq_integral_energy (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m T : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hT : 0 ≤ T) (x : FeatureIndex n → ℝ) :
    physicalFilledOverlap n d L steps ha hm T T x -
      physicalFilledOverlap n d L steps ha hm T 0 x =
      ∫ t in 0..T, physicalFilledOverlapEnergy n d L steps ha hm T t x := by
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (physicalFilledOverlap_continuous n d L steps ha hm T x).continuousOn
    (fun t ht => physicalFilledOverlap_hasDerivAt n d L steps ha hm ht x)
    ((physicalFilledOverlapEnergy_continuous n d L steps ha hm T x).intervalIntegrable 0 T)).symm

def physicalUnitFieldDriver (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] (FeatureIndex n → ℝ) :=
  Real.sqrt (n : ℝ) • physicalNormalizedSourceMap n

def physicalFilledFieldHessian (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex (n + 1) → ℝ) (z : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
  clockGradient m
    (fun y => gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1)) steps
      (x + physicalUnitFieldDriver (n + 1) y))
    (fun y => gaussianHierarchyMean (uniformWeight (n + 1)) (finiteFeature (n + 1))
      (fun σ => normalizedSpin (n + 1) σ j) steps (x + physicalUnitFieldDriver (n + 1) y))
    (fun y => gaussianHierarchyMean (uniformWeight (n + 1)) (finiteFeature (n + 1))
      (fun σ => normalizedSpin (n + 1) σ i) steps (x + physicalUnitFieldDriver (n + 1) y))
    (fun y => hierarchySourceHessianMatrix (uniformWeight (n + 1)) (finiteFeature (n + 1))
      (physicalNormalizedSourceMap (n + 1)) steps (x + physicalUnitFieldDriver (n + 1) y) i j)
    (T - t) z

theorem clockGradient_mul_source {ι : Type*} [Fintype ι]
    (c m : ℝ) (F G A A₁ : (ι → ℝ) → ℝ) (t : ℝ) (z : ι → ℝ) :
    clockGradient m F (fun y => c * G y) A (fun y => c * A₁ y) t z =
      c * clockGradient m F G A A₁ t z := by
  unfold clockGradient
  have he : (fun y => A y * (c * G y)) = (fun y => c * (A y * G y)) := by
    funext y
    ring
  rw [he, clockTest_const_mul, clockTest_const_mul, clockTest_const_mul]
  ring

theorem physicalUnitFieldDriver_feature (n : ℕ) (σ : Spin n) (j : Fin n) :
    finiteFeature n σ (physicalUnitFieldDriver n (Pi.single j 1)) =
      Real.sqrt (n : ℝ) * normalizedSpin n σ j := by
  simp only [physicalUnitFieldDriver, ContinuousLinearMap.smul_apply,
    map_smul, smul_eq_mul, physicalNormalizedSourceMap_feature]

theorem physicalFieldJet_G (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex (n + 1) → ℝ)
    (i j : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
    (physicalSpinFeatureJet (n + 1) n i (physicalUnitFieldDriver (n + 1)) steps ha x).G j z =
      Real.sqrt (n + 1 : ℝ) * gaussianHierarchyMean (uniformWeight (n + 1))
        (finiteFeature (n + 1)) (fun σ => normalizedSpin (n + 1) σ j) steps
        (x + physicalUnitFieldDriver (n + 1) z) := by
  change gaussianHierarchyMean _ _
    (fun σ => finiteFeature (n + 1) σ (physicalUnitFieldDriver (n + 1) (Pi.single j 1)))
    steps _ = _
  simp only [physicalUnitFieldDriver_feature, Nat.cast_add, Nat.cast_one]
  exact congrFun (gaussianHierarchyMean_const_mul_ordered (uniformWeight_pos (n + 1))
    _ _ steps ha _) _

theorem physicalFieldJet_A₁ (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a steps) (x : FeatureIndex (n + 1) → ℝ)
    (i j : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
    (physicalSpinFeatureJet (n + 1) n i (physicalUnitFieldDriver (n + 1)) steps ha x).A₁ j z =
      Real.sqrt (n + 1 : ℝ) * hierarchySourceHessianMatrix (uniformWeight (n + 1))
        (finiteFeature (n + 1)) (physicalNormalizedSourceMap (n + 1)) steps
        (x + physicalUnitFieldDriver (n + 1) z) i j := by
  rw [physicalSpinFeatureJet, gaussianFeatureJet_A₁]
  have he : (fun σ => normalizedSpin (n + 1) σ i) =
      (fun σ => finiteFeature (n + 1) σ (physicalNormalizedSourceMap (n + 1) (Pi.single i 1))) := by
    funext σ
    exact (physicalNormalizedSourceMap_feature (n + 1) σ i).symm
  rw [he]
  change gaussianHierarchyHessian _ _ steps _ _
    (Real.sqrt ((n + 1 : ℕ) : ℝ) • physicalNormalizedSourceMap (n + 1) (Pi.single j 1)) = _
  simpa only [hierarchySourceHessianMatrix, Nat.cast_add, Nat.cast_one] using
    gaussianHierarchyHessian_smul_right (uniformWeight_pos (n + 1)) _ steps ha
      (x + physicalUnitFieldDriver (n + 1) z)
      (physicalNormalizedSourceMap (n + 1) (Pi.single i 1))
      (physicalNormalizedSourceMap (n + 1) (Pi.single j 1)) (Real.sqrt ((n + 1 : ℕ) : ℝ))

theorem physicalFieldJet_evolve_A₁ (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex (n + 1) → ℝ) (i j : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
    ((physicalSpinFeatureJet (n + 1) n i (physicalUnitFieldDriver (n + 1)) steps ha x).evolve
      hm (T - t)).A₁ j z = Real.sqrt (n + 1 : ℝ) *
        physicalFilledFieldHessian n steps ha hm T t x z i j := by
  change clockGradient m _ _ _ _ (T - t) z = _
  have hG := funext (physicalFieldJet_G n steps ha x i j)
  have hA₁ := funext (physicalFieldJet_A₁ n steps ha x i j)
  rw [hG, hA₁, clockGradient_mul_source]
  rfl

theorem physicalFieldJet_evolve_energy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex (n + 1) → ℝ) (i : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
    ((physicalSpinFeatureJet (n + 1) n i (physicalUnitFieldDriver (n + 1)) steps ha x).evolve
      hm (T - t)).energy z = (n + 1 : ℝ) *
        ∑ j, (physicalFilledFieldHessian n steps ha hm T t x z i j) ^ 2 := by
  simp only [HeatJet.energy, physicalFieldJet_evolve_A₁, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ (n + 1 : ℝ)), Finset.mul_sum]

def physicalFilledFieldTraceExpectation (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex (n + 1) → ℝ) : ℝ :=
  ∑ i, clockTest m
    ((physicalSpinFeatureJet (n + 1) n i (physicalUnitFieldDriver (n + 1)) steps ha x).evolve
      hm (T - t)).F
    (fun z => ∑ j, (physicalFilledFieldHessian n steps ha hm T t x z i j) ^ 2) t 0

theorem physicalFilledOverlapEnergy_eq_fieldTrace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex (n + 1) → ℝ) :
    physicalFilledOverlapEnergy (n + 1) n (physicalUnitFieldDriver (n + 1)) steps ha hm T t x =
      (n + 1 : ℝ) * physicalFilledFieldTraceExpectation n steps ha hm T t x := by
  simp only [physicalFilledOverlapEnergy, HeatJet.filledEnergy,
    physicalFilledFieldTraceExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := funext (physicalFieldJet_evolve_energy n steps ha hm T t x i)
  rw [he, clockTest_const_mul]

theorem physicalFilledOverlap_hasDerivAt_fieldTrace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m T t : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (ht : t ∈ Ioo 0 T)
    (x : FeatureIndex (n + 1) → ℝ) :
    HasDerivAt (fun s => physicalFilledOverlap (n + 1) n (physicalUnitFieldDriver (n + 1))
      steps ha hm T s x) ((n + 1 : ℝ) * physicalFilledFieldTraceExpectation n steps ha hm T t x) t := by
  rw [← physicalFilledOverlapEnergy_eq_fieldTrace]
  exact physicalFilledOverlap_hasDerivAt (n + 1) n _ steps ha hm ht x

theorem physicalFilledOverlap_increment_eq_integral_fieldTrace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m T : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hT : 0 ≤ T)
    (x : FeatureIndex (n + 1) → ℝ) :
    physicalFilledOverlap (n + 1) n (physicalUnitFieldDriver (n + 1)) steps ha hm T T x -
      physicalFilledOverlap (n + 1) n (physicalUnitFieldDriver (n + 1)) steps ha hm T 0 x =
      (n + 1 : ℝ) * ∫ t in 0..T, physicalFilledFieldTraceExpectation n steps ha hm T t x := by
  rw [physicalFilledOverlap_increment_eq_integral_energy _ _ _ _ ha hm hT x]
  simp_rw [physicalFilledOverlapEnergy_eq_fieldTrace]
  exact intervalIntegral.integral_const_mul _ _

def physicalFilledSourceHessian (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) (m T t : ℝ)
    (x : FeatureIndex n → ℝ) (z : Fin (d + 1) → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  clockGradient m
    (fun y => gaussianHierarchy (uniformWeight n) (finiteFeature n) steps (x + L y))
    (fun y => actualSpinMean n steps (x + L y) j)
    (fun y => actualSpinMean n steps (x + L y) i)
    (fun y => hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps (x + L y) i j) (T - t) z

theorem physicalSourceHessian_eq_response (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ) (i j : Fin n) :
    hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
      (physicalNormalizedSourceMap n) steps x i j =
      gaussianHierarchyResponse (uniformWeight n) (finiteFeature n)
        (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1)) steps x := by
  simp only [hierarchySourceHessianMatrix, gaussianHierarchyHessian,
    physicalNormalizedSourceMap_feature]

theorem physicalJointJet_G (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a γ : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (i j : Fin n) (k : Fin (d + 1))
    (hcol : L (Pi.single k 1) = γ • physicalNormalizedSourceMap n (Pi.single j 1))
    (z : Fin (d + 1) → ℝ) :
    (physicalSpinFeatureJet n d i L steps ha x).G k z = γ * actualSpinMean n steps (x + L z) j := by
  change gaussianHierarchyMean _ _ (fun σ => finiteFeature n σ (L (Pi.single k 1))) steps _ = _
  simp only [hcol, map_smul, smul_eq_mul, physicalNormalizedSourceMap_feature]
  exact congrFun (gaussianHierarchyMean_const_mul_ordered (uniformWeight_pos n)
    _ _ steps ha γ) _

theorem physicalJointJet_A₁ (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a γ : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n → ℝ) (i j : Fin n) (k : Fin (d + 1))
    (hcol : L (Pi.single k 1) = γ • physicalNormalizedSourceMap n (Pi.single j 1))
    (z : Fin (d + 1) → ℝ) :
    (physicalSpinFeatureJet n d i L steps ha x).A₁ k z = γ *
      hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
        (physicalNormalizedSourceMap n) steps (x + L z) i j := by
  rw [physicalSpinFeatureJet, gaussianFeatureJet_A₁, hcol]
  have he : (fun σ => normalizedSpin n σ i) =
      (fun σ => finiteFeature n σ (physicalNormalizedSourceMap n (Pi.single i 1))) := by
    funext σ
    exact (physicalNormalizedSourceMap_feature n σ i).symm
  rw [he]
  exact gaussianHierarchyHessian_smul_right (uniformWeight_pos n) _ steps ha _ _ _ γ

theorem physicalJointJet_evolve_A₁ (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m γ : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex n → ℝ) (i j : Fin n) (k : Fin (d + 1))
    (hcol : L (Pi.single k 1) = γ • physicalNormalizedSourceMap n (Pi.single j 1))
    (z : Fin (d + 1) → ℝ) :
    ((physicalSpinFeatureJet n d i L steps ha x).evolve hm (T - t)).A₁ k z =
      γ * physicalFilledSourceHessian n d L steps m T t x z i j := by
  change clockGradient m _ _ _ _ (T - t) z = _
  rw [funext (physicalJointJet_G n d L steps ha x i j k hcol),
    funext (physicalJointJet_A₁ n d L steps ha x i j k hcol), clockGradient_mul_source]
  rfl

theorem physicalJointJet_energy_ge_fieldTrace (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m γ : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex n → ℝ) (i : Fin n) (field : Fin n → Fin (d + 1))
    (hfield : Function.Injective field)
    (hcol : ∀ j, L (Pi.single (field j) 1) = γ • physicalNormalizedSourceMap n (Pi.single j 1))
    (z : Fin (d + 1) → ℝ) :
    γ ^ 2 * ∑ j, (physicalFilledSourceHessian n d L steps m T t x z i j) ^ 2 ≤
      ((physicalSpinFeatureJet n d i L steps ha x).evolve hm (T - t)).energy z := by
  classical
  let f (k : Fin (d + 1)) :=
    (((physicalSpinFeatureJet n d i L steps ha x).evolve hm (T - t)).A₁ k z) ^ 2
  have he : ∑ j, f (field j) = γ ^ 2 *
      ∑ j, (physicalFilledSourceHessian n d L steps m T t x z i j) ^ 2 := by
    simp only [f, physicalJointJet_evolve_A₁ n d L steps ha hm T t x i _ _ (hcol _),
      mul_pow, Finset.mul_sum]
  rw [← he]
  change ∑ j, f (field j) ≤ ∑ k, f k
  rw [← Finset.sum_image (fun j _ j' _ h => hfield h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => sq_nonneg _)

theorem physicalFilledSourceHessian_smooth (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m T t : ℝ) (x : FeatureIndex n → ℝ) (i j : Fin n) :
    BddSmooth 0 (fun z => physicalFilledSourceHessian n d L steps m T t x z i j) := by
  let J := physicalSpinFeatureJet n d i L steps ha x
  have hG := (gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ j) steps ha 0).affine_zero L x
  have hH := (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1))
    steps ha 0).affine_zero L x
  simpa only [physicalFilledSourceHessian, actualSpinMean, physicalSourceHessian_eq_response,
    J, physicalSpinFeatureJet, gaussianFeatureJet_F, gaussianFeatureJet_A] using
    clockGradient_bddSmooth J.regular hG J.smoothA hH m (T - t)

def physicalFilledSourceTraceExpectation (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex n → ℝ) : ℝ :=
  ∑ i, clockTest m ((physicalSpinFeatureJet n d i L steps ha x).evolve hm (T - t)).F
    (fun z => ∑ j, (physicalFilledSourceHessian n d L steps m T t x z i j) ^ 2) t 0

theorem physicalFilledOverlapEnergy_ge_sourceTrace (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m γ : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ)
    (x : FeatureIndex n → ℝ) (field : Fin n → Fin (d + 1))
    (hfield : Function.Injective field)
    (hcol : ∀ j, L (Pi.single (field j) 1) = γ • physicalNormalizedSourceMap n (Pi.single j 1)) :
    γ ^ 2 * physicalFilledSourceTraceExpectation n d L steps ha hm T t x ≤
      physicalFilledOverlapEnergy n d L steps ha hm T t x := by
  simp only [physicalFilledSourceTraceExpectation, physicalFilledOverlapEnergy,
    HeatJet.filledEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let J := (physicalSpinFeatureJet n d i L steps ha x).evolve hm (T - t)
  have htest : BddSmooth 0 (fun z => ∑ j,
      (physicalFilledSourceHessian n d L steps m T t x z i j) ^ 2) := by
    apply BddSmooth.sum Finset.univ
    intro j _
    simpa only [pow_two] using
      (physicalFilledSourceHessian_smooth n d L steps ha m T t x i j).mul
        (physicalFilledSourceHessian_smooth n d L steps ha m T t x i j)
  rw [← clockTest_const_mul]
  exact shiftedMean_mono (htest.const_mul (γ ^ 2)) J.smoothEnergy
    (fun z => physicalJointJet_energy_ge_fieldTrace n d L steps ha hm T t x i field hfield hcol z)
    ((exponentialIncrement_gaussian (fun _ => Real.toNNReal t)).integrable_shift J.lipschitz m 0)

theorem physicalFilledOverlapEnergy_ge_fieldClockTrace (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m c : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hc : 0 ≤ c) (T t : ℝ)
    (x : FeatureIndex n → ℝ) (field : Fin n → Fin (d + 1))
    (hfield : Function.Injective field)
    (hcol : ∀ j, L (Pi.single (field j) 1) = Real.sqrt ((n : ℝ) * c) •
      physicalNormalizedSourceMap n (Pi.single j 1)) :
    (n : ℝ) * c * physicalFilledSourceTraceExpectation n d L steps ha hm T t x ≤
      physicalFilledOverlapEnergy n d L steps ha hm T t x := by
  simpa only [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hc)] using
    physicalFilledOverlapEnergy_ge_sourceTrace n d L steps ha hm T t x field hfield hcol

theorem physicalUnitFieldDriver_single (n : ℕ) (hn : 0 < n) (j : Fin n) :
    physicalUnitFieldDriver n (Pi.single j 1) = Pi.single (Sum.inl j) 1 := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  ext k
  cases k with
  | inl k =>
    change Real.sqrt (n : ℝ) * ((Pi.single j 1 : Fin n → ℝ) k / Real.sqrt (n : ℝ)) =
      (Pi.single (Sum.inl j) 1 : FeatureIndex n → ℝ) (Sum.inl k)
    rw [mul_div_cancel₀ _ hs]
    simp only [Pi.single_apply, Sum.inl.injEq]
  | inr k =>
    change Real.sqrt (n : ℝ) * 0 = (Pi.single (Sum.inl j) 1 : FeatureIndex n → ℝ) (Sum.inr k)
    simp

def physicalJointGaussianDriver (n d : ℕ) (e : Fin (d + 1) ≃ FeatureIndex n)
    (q : FeatureIndex n → ℝ≥0) :
    (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ) :=
  (scaleDriver q).comp (coordinateEquiv e).toContinuousLinearMap

theorem physicalJointGaussianDriver_field_column (n d : ℕ) (hn : 0 < n)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (c : ℝ≥0) (hc : ∀ j, q (Sum.inl j) = c) (j : Fin n) :
    physicalJointGaussianDriver n d e q (Pi.single (e.symm (Sum.inl j)) 1) =
      Real.sqrt ((n : ℝ) * c) • physicalNormalizedSourceMap n (Pi.single j 1) := by
  have he : physicalJointGaussianDriver n d e q (Pi.single (e.symm (Sum.inl j)) 1) =
      Real.sqrt (c : ℝ) • Pi.single (Sum.inl j) 1 := by
    simp only [physicalJointGaussianDriver, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, coordinateEquiv_single, Equiv.apply_symm_apply]
    ext k
    by_cases hk : k = Sum.inl j
    · subst k
      simp [hc, scaleDriver_apply]
    · simp [scaleDriver_apply, Pi.single_apply, hk]
  rw [he, ← physicalUnitFieldDriver_single n hn j, physicalUnitFieldDriver,
    ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  rw [Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

theorem physicalJointGaussianDriver_energy_ge_fieldClockTrace (n d : ℕ) (hn : 0 < n)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (c : ℝ≥0) (hc : ∀ j, q (Sum.inl j) = c)
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    (n : ℝ) * c * physicalFilledSourceTraceExpectation n d
      (physicalJointGaussianDriver n d e q) steps ha hm T t x ≤
      physicalFilledOverlapEnergy n d (physicalJointGaussianDriver n d e q) steps ha hm T t x := by
  exact physicalFilledOverlapEnergy_ge_fieldClockTrace n d _ steps ha hm c.coe_nonneg T t x
    (fun j => e.symm (Sum.inl j))
    (fun j j' h => Sum.inl.inj (e.symm.injective h))
    (physicalJointGaussianDriver_field_column n d hn e q c hc)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
