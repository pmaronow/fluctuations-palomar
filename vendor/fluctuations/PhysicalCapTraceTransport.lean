module

public import ParameterizedClockContinuity
public import PhysicalJointSusceptibilityBands

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

theorem physicalFilledSourceHessian_source_shift (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m T t : ℝ) (x : FeatureIndex n → ℝ)
    (z : Fin (d + 1) → ℝ) (i j : Fin n) :
    physicalFilledSourceHessian n d L steps m T t x z i j =
      physicalFilledSourceHessian n d L steps m (T - t) 0 (x + L z) 0 i j := by
  rw [physicalFilledSourceHessian_eq_linearGradient n d L steps ha,
    physicalFilledSourceHessian_eq_linearGradient n d L steps ha]
  simp only [sub_zero, map_zero, add_zero]

theorem physicalFilledSourceHessian_joint_continuous (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m : ℝ) (i j : Fin n) :
    Continuous (fun p : ℝ × (FeatureIndex n → ℝ) =>
      physicalFilledSourceHessian n d L steps m p.1 0 p.2 0 i j) := by
  obtain ⟨C, hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) steps ha
  have hA := gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) steps ha 0
  have hG := gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ j) steps ha 0
  have hH := gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1)) steps ha 0
  let addL (p : (FeatureIndex n → ℝ) × (Fin (d + 1) → ℝ)) := p.1 + L p.2
  have hc : Continuous addL := continuous_fst.add (L.continuous.comp continuous_snd)
  have hFl : ∀ x : FeatureIndex n → ℝ,
      LipschitzWith (C * (1 * ‖L‖₊)) (fun y => gaussianHierarchy (uniformWeight n) (finiteFeature n)
        steps (x + L y)) := fun x =>
    hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)
  have hh := parameter_clockGradient_continuous
    (G := fun x y => actualSpinMean n steps (x + L y) j)
    (A := fun x y => actualSpinMean n steps (x + L y) i)
    (B := fun x y => gaussianHierarchyResponse (uniformWeight n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1)) steps (x + L y))
    hFl (hF.continuous.comp hc)
    (hG.continuous.comp hc) (hA.continuous.comp hc) (hH.continuous.comp hc)
    (AbsBounded.precomp hG.bound addL) (AbsBounded.precomp hA.bound addL)
    (AbsBounded.precomp hH.bound addL) m 0
  simpa only [physicalFilledSourceHessian, actualSpinMean, physicalSourceHessian_eq_response,
    addL, sub_zero] using hh

theorem physicalFilledSourceHessian_joint_bounded (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m : ℝ) (i j : Fin n) :
    AbsBounded (fun p : ℝ × (FeatureIndex n → ℝ) =>
      physicalFilledSourceHessian n d L steps m p.1 0 p.2 0 i j) := by
  obtain ⟨C, hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) steps ha
  have hA := gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) steps ha 0
  have hG := gaussianHierarchyMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ j) steps ha 0
  have hH := gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1)) steps ha 0
  obtain ⟨KA, hKA, bA⟩ := hA.bound
  obtain ⟨KG, hKG, bG⟩ := hG.bound
  obtain ⟨KH, hKH, bH⟩ := hH.bound
  refine ⟨KH + 2 * |m| * KA * KG, by positivity, ?_⟩
  intro p
  simpa only [physicalFilledSourceHessian, actualSpinMean, physicalSourceHessian_eq_response,
    sub_zero, Function.comp_def] using clockGradient_abs_le
      (hF.comp ((isometry_add_left p.2).lipschitzWith.comp L.lipschitzWith))
      (hG.affine_zero L p.2) (hA.affine_zero L p.2) (hH.affine_zero L p.2)
      hKG hKA (fun y => bG _) (fun y => bA _) (fun y => bH _) m p.1 0

theorem physicalLinearClockContinuation_joint_continuous (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a steps) (m : ℝ) :
    Continuous (fun p : ℝ × (FeatureIndex n → ℝ) => linearClockContinuation L m
      (gaussianHierarchy (uniformWeight n) (finiteFeature n) steps) p.1 p.2) := by
  obtain ⟨C, hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) steps ha
  have hc : Continuous (fun p : (FeatureIndex n → ℝ) × (Fin (d + 1) → ℝ) =>
      gaussianHierarchy (uniformWeight n) (finiteFeature n) steps (p.1 + L p.2)) :=
    hF.continuous.comp (continuous_fst.add (L.continuous.comp continuous_snd))
  have hh := parameter_clockContinuation_continuous
    (fun x => hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)) hc m 0
  convert hh using 1
  ext p
  exact linearClockContinuation_eq L hF.continuous m p.1 p.2

theorem physicalFilledSourceTraceExpectation_joint_continuous (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) :
    Continuous (fun p : ℝ × (FeatureIndex n → ℝ) =>
      physicalFilledSourceTraceExpectation n d L steps ha hm T p.1 p.2) := by
  obtain ⟨C, hBase⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) steps ha
  let base := gaussianHierarchy (uniformWeight n) (finiteFeature n) steps
  let F (p : ℝ × (FeatureIndex n → ℝ)) (y : Fin (d + 1) → ℝ) :=
    linearClockContinuation L m base p.1 (p.2 + L y)
  have hF : ∀ p, LipschitzWith (C * (1 * ‖L‖₊)) (F p) := by
    intro p
    have hlc := lipschitzWith_shiftedContinuation hBase hm
      (fun x => (exponentialIncrement_linearGaussian L (Real.toNNReal p.1)).integrable_shift hBase m x)
    exact hlc.comp ((isometry_add_left p.2).lipschitzWith.comp L.lipschitzWith)
  have hmap : Continuous (fun p : (ℝ × (FeatureIndex n → ℝ)) × (Fin (d + 1) → ℝ) =>
      (p.1.1, p.1.2 + L p.2)) := by fun_prop
  have hcF : Continuous (fun p : (ℝ × (FeatureIndex n → ℝ)) × (Fin (d + 1) → ℝ) => F p.1 p.2) :=
    (physicalLinearClockContinuation_joint_continuous n d L steps ha m).comp hmap
  apply continuous_finsetSum
  intro i _
  let A (p : ℝ × (FeatureIndex n → ℝ)) (y : Fin (d + 1) → ℝ) :=
    ∑ j, (physicalFilledSourceHessian n d L steps m p.1 0 p.2 y i j) ^ 2
  have hcA : Continuous (fun p : (ℝ × (FeatureIndex n → ℝ)) × (Fin (d + 1) → ℝ) => A p.1 p.2) := by
    apply continuous_finsetSum
    intro j _
    have hh := ((physicalFilledSourceHessian_joint_continuous n d L steps ha m i j).comp hmap).pow 2
    convert hh using 1
    ext p
    rw [physicalFilledSourceHessian_source_shift n d L steps ha m]
    simp only [sub_zero, Function.comp_def, Pi.pow_apply]
  have hbA : AbsBounded (fun p : (ℝ × (FeatureIndex n → ℝ)) × (Fin (d + 1) → ℝ) => A p.1 p.2) := by
    apply AbsBounded.sum
    intro j
    have hh := AbsBounded.precomp (physicalFilledSourceHessian_joint_bounded n d L steps ha m i j)
      (fun p : (ℝ × (FeatureIndex n → ℝ)) × (Fin (d + 1) → ℝ) => (p.1.1, p.1.2 + L p.2))
    have hh2 := hh.mul hh
    convert hh2 using 1
    ext p
    rw [physicalFilledSourceHessian_source_shift n d L steps ha m]
    simp only [sub_zero, pow_two]
  obtain ⟨K, _, hbK⟩ := hbA
  have hh := parameter_clockTest_continuous (F := F) (A := A) hF hcF hcA
    (fun p y => hbK (p, y)) m 0
  have hout : Continuous (fun p : ℝ × (FeatureIndex n → ℝ) => (p.1, (T - p.1, p.2))) := by fun_prop
  convert hh.comp hout using 1
  ext p
  simp only [Function.comp_def]
  have he : F (T - p.1, p.2) =
      ((physicalSpinFeatureJet n d i L steps ha p.2).evolve hm (T - p.1)).F := by
    ext y
    exact linearClockContinuation_affine L hBase.continuous m (T - p.1) p.2 y
  rw [he]
  simp only [A, physicalFilledSourceHessian, sub_zero]

theorem physicalFilledSourceTraceExpectation_joint_bounded (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) :
    AbsBounded (fun p : ℝ × (FeatureIndex n → ℝ) =>
      physicalFilledSourceTraceExpectation n d L steps ha hm T p.1 p.2) := by
  apply AbsBounded.sum
  intro i
  have hbA : AbsBounded (fun p : (ℝ × (FeatureIndex n → ℝ)) × (Fin (d + 1) → ℝ) =>
      ∑ j, (physicalFilledSourceHessian n d L steps m T p.1.1 p.1.2 p.2 i j) ^ 2) := by
    apply AbsBounded.sum
    intro j
    have hh := AbsBounded.precomp (physicalFilledSourceHessian_joint_bounded n d L steps ha m i j)
      (fun p : (ℝ × (FeatureIndex n → ℝ)) × (Fin (d + 1) → ℝ) => (T - p.1.1, p.1.2 + L p.2))
    convert hh.mul hh using 1
    ext p
    rw [physicalFilledSourceHessian_source_shift n d L steps ha m]
    simp only [pow_two]
  obtain ⟨K, hK, hbK⟩ := hbA
  refine ⟨K, hK, ?_⟩
  intro p
  let J := (physicalSpinFeatureJet n d i L steps ha p.2).evolve hm (T - p.1)
  apply clockTest_abs_le J.lipschitz
  · apply BddSmooth.sum Finset.univ
    intro j _
    simpa only [pow_two] using
      (physicalFilledSourceHessian_smooth n d L steps ha m T p.1 p.2 i j).mul
        (physicalFilledSourceHessian_smooth n d L steps ha m T p.1 p.2 i j)
  · exact fun y => hbK (p, y)

theorem physicalFilledSourceTrace_integral_smooth (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T : ℝ) :
    BddSmooth 0 (fun x => ∫ t in 0..1, physicalFilledSourceTraceExpectation n d L steps ha hm T t x) := by
  obtain ⟨K, hK, hbK⟩ := physicalFilledSourceTraceExpectation_joint_bounded n d L steps ha hm T
  have hc := (physicalFilledSourceTraceExpectation_joint_continuous n d L steps ha hm T).comp
    (continuous_snd.prodMk continuous_fst)
  refine ⟨intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x t => physicalFilledSourceTraceExpectation n d L steps ha hm T t x)
    (by simpa only [Function.uncurry_def, Function.comp_def] using hc) 0 1, K, hK, ?_⟩
  intro x
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := K)
      (f := fun t => physicalFilledSourceTraceExpectation n d L steps ha hm T t x) (fun t _ => by
      simpa only [Real.norm_eq_abs] using hbK (t, x))

theorem physicalFilledSourceTraceExpectation_nonneg (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    0 ≤ physicalFilledSourceTraceExpectation n d L steps ha hm T t x := by
  apply Finset.sum_nonneg
  intro i _
  apply clockTest_nonneg ((physicalSpinFeatureJet n d i L steps ha x).evolve hm (T - t)).lipschitz
  intro y
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem physicalJointGaussianDriver_integral_trace_le_energy (n d : ℕ) (hn : 0 < n)
    (e : Fin (d + 1) ≃ FeatureIndex n) (q : FeatureIndex n → ℝ≥0)
    (c : ℝ≥0) (hfield : ∀ j, q (Sum.inl j) = c)
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (x : FeatureIndex n → ℝ) :
    (n : ℝ) * c * (∫ t in 0..1, physicalFilledSourceTraceExpectation n d
      (physicalJointGaussianDriver n d e q) steps ha hm 1 t x) ≤
      ∫ t in 0..1, physicalFilledOverlapEnergy n d (physicalJointGaussianDriver n d e q)
        steps ha hm 1 t x := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (((physicalFilledSourceTraceExpectation_continuous n d _ steps ha hm 1 x).intervalIntegrable 0 1).const_mul
      ((n : ℝ) * c))
    ((physicalFilledOverlapEnergy_continuous n d _ steps ha hm 1 x).intervalIntegrable 0 1)
    (fun t _ => physicalJointGaussianDriver_energy_ge_fieldClockTrace n d hn e q c hfield
      steps ha hm 1 t x)
  rwa [intervalIntegral.integral_const_mul] at h

def physicalFiniteCapFieldTrace (n d : ℕ) (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) :
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) → {a : ℝ} →
      OrderedSteps a (pre ++ tail) → (FeatureIndex (n + 1) → ℝ) → ℝ
  | [], _, _, _, _ => 0
  | (m, q) :: pre, tail, _, ha, x =>
      (n + 1 : ℝ) * q (Sum.inl 0) *
        (∫ t in 0..1, physicalFilledSourceTraceExpectation (n + 1) d
          (physicalJointGaussianDriver (n + 1) d e q) (pre ++ tail) ha.2.2.2 ha.2.2.1 1 t x) +
      shiftedMean (Measure.pi fun k => gaussianReal 0 (q k)) m
        (gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1)) (pre ++ tail))
        (physicalFiniteCapFieldTrace n d e pre tail ha.2.2.2) x

theorem physicalFiniteCapFieldTrace_smooth (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1))
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) :
    BddSmooth 0 (physicalFiniteCapFieldTrace n d e pre tail ha) := by
  induction pre generalizing a with
  | nil => exact BddSmooth.const 0 0
  | cons st pre ih =>
    rcases st with ⟨m, q⟩
    exact ((physicalFilledSourceTrace_integral_smooth (n + 1) d _ (pre ++ tail)
      ha.2.2.2 ha.2.2.1 1).const_mul ((n + 1 : ℝ) * q (Sum.inl 0))).add
        ((ih ha.2.2.2).shiftedMean
          (gaussianHierarchy_regular (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
            (pre ++ tail) ha.2.2.2 0)
          (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
            (pre ++ tail) ha.2.2.2 m q))

theorem physicalFiniteCapFieldTrace_le_energy (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1))
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail))
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (x : FeatureIndex (n + 1) → ℝ) :
    physicalFiniteCapFieldTrace n d e pre tail ha x ≤
      physicalFiniteCapEnergy (n + 1) d e pre tail ha x := by
  induction pre generalizing a x with
  | nil => exact le_rfl
  | cons st pre ih =>
    rcases st with ⟨m, q⟩
    apply add_le_add
    · simpa only [Nat.cast_add, Nat.cast_one] using
        physicalJointGaussianDriver_integral_trace_le_energy (n + 1) d (by omega) e q
        (q (Sum.inl 0)) (hfield (m, q) (by simp)) (pre ++ tail) ha.2.2.2 ha.2.2.1 x
    · exact shiftedMean_mono (physicalFiniteCapFieldTrace_smooth n d e pre tail ha.2.2.2)
        (physicalFiniteCapEnergy_smooth (n + 1) d e pre tail ha.2.2.2)
        (ih ha.2.2.2 (fun st hs => hfield st (List.mem_cons_of_mem _ hs)))
        (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
          (pre ++ tail) ha.2.2.2 m q x)

theorem physicalFiniteCapFieldTrace_rooted_le_endpoint (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (q₀ : FeatureIndex (n + 1) → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a M : ℝ}
    (ha : OrderedSteps a (pre ++ tail))
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (x : FeatureIndex (n + 1) → ℝ)
    (hmean : zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (prefixTest pre (gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1)) tail)
        (physicalSpinMeanSq (n + 1) tail)) x ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapFieldTrace n d e pre tail ha) x ≤ M := by
  apply le_trans ?_ (physicalFiniteCapEnergy_rooted_le_endpoint (n + 1) d e q₀ pre tail ha x hmean)
  have hmap : Measurable (fun z : FeatureIndex (n + 1) → ℝ => x + z) := measurable_const.add measurable_id
  exact integral_mono
    ((physicalFiniteCapFieldTrace_smooth n d e pre tail ha).integrable_comp_measurable hmap)
    ((physicalFiniteCapEnergy_smooth (n + 1) d e pre tail ha).integrable_comp_measurable hmap)
    (fun z => physicalFiniteCapFieldTrace_le_energy n d e pre tail ha hfield (x + z))

def physicalFiniteCapRadiusTrace (n d : ℕ) (e : Fin (d + 1) ≃ FeatureIndex (n + 1))
    (duration : GaussianStep (FeatureIndex (n + 1)) → ℝ≥0) :
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) → {a : ℝ} →
      OrderedSteps a (pre ++ tail) → (FeatureIndex (n + 1) → ℝ) → ℝ
  | [], _, _, _, _ => 0
  | (m, q) :: pre, tail, _, ha, x =>
      duration (m, q) *
        (∫ t in 0..1, physicalFilledSourceTraceExpectation (n + 1) d
          (physicalJointGaussianDriver (n + 1) d e q) (pre ++ tail) ha.2.2.2 ha.2.2.1 1 t x) +
      shiftedMean (Measure.pi fun k => gaussianReal 0 (q k)) m
        (gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1)) (pre ++ tail))
        (physicalFiniteCapRadiusTrace n d e duration pre tail ha.2.2.2) x

theorem physicalFiniteCapRadiusTrace_smooth (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1))
    (duration : GaussianStep (FeatureIndex (n + 1)) → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) :
    BddSmooth 0 (physicalFiniteCapRadiusTrace n d e duration pre tail ha) := by
  induction pre generalizing a with
  | nil => exact BddSmooth.const 0 0
  | cons st pre ih =>
    rcases st with ⟨m, q⟩
    exact ((physicalFilledSourceTrace_integral_smooth (n + 1) d _ (pre ++ tail)
      ha.2.2.2 ha.2.2.1 1).const_mul (duration (m, q))).add
        ((ih ha.2.2.2).shiftedMean
          (gaussianHierarchy_regular (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
            (pre ++ tail) ha.2.2.2 0)
          (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
            (pre ++ tail) ha.2.2.2 m q))

theorem physicalFiniteCapRadiusTrace_le_fieldTrace (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1))
    (duration : GaussianStep (FeatureIndex (n + 1)) → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a g : ℝ}
    (ha : OrderedSteps a (pre ++ tail))
    (hslope : ∀ st ∈ pre, g * duration st ≤ st.2 (Sum.inl 0))
    (x : FeatureIndex (n + 1) → ℝ) :
    (n + 1 : ℝ) * g * physicalFiniteCapRadiusTrace n d e duration pre tail ha x ≤
      physicalFiniteCapFieldTrace n d e pre tail ha x := by
  induction pre generalizing a x with
  | nil => simp [physicalFiniteCapRadiusTrace, physicalFiniteCapFieldTrace]
  | cons st pre ih =>
    rcases st with ⟨m, q⟩
    change (n + 1 : ℝ) * g * (_ + _) ≤ _ + _
    rw [mul_add]
    apply add_le_add
    · have hI : 0 ≤ ∫ t in 0..1, physicalFilledSourceTraceExpectation (n + 1) d
          (physicalJointGaussianDriver (n + 1) d e q) (pre ++ tail) ha.2.2.2 ha.2.2.1 1 t x := by
        apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        intro t _
        exact physicalFilledSourceTraceExpectation_nonneg (n + 1) d _ (pre ++ tail)
          ha.2.2.2 ha.2.2.1 1 t x
      have hs := mul_le_mul_of_nonneg_left (hslope (m, q) (by simp)) (by positivity : 0 ≤ (n + 1 : ℝ))
      nlinarith [mul_le_mul_of_nonneg_right hs hI]
    · rw [← shiftedMean_const_mul]
      exact shiftedMean_mono
        ((physicalFiniteCapRadiusTrace_smooth n d e duration pre tail ha.2.2.2).const_mul ((n + 1 : ℝ) * g))
        (physicalFiniteCapFieldTrace_smooth n d e pre tail ha.2.2.2)
        (ih ha.2.2.2 (fun st hs => hslope st (List.mem_cons_of_mem _ hs)))
        (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
          (pre ++ tail) ha.2.2.2 m q x)

theorem physicalFiniteCapRadiusTrace_rooted_le_endpoint (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (q₀ : FeatureIndex (n + 1) → ℝ≥0)
    (duration : GaussianStep (FeatureIndex (n + 1)) → ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a g M : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (hg : 0 < g)
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : ∀ st ∈ pre, g * duration st ≤ st.2 (Sum.inl 0))
    (x : FeatureIndex (n + 1) → ℝ)
    (hmean : zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (prefixTest pre (gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1)) tail)
        (physicalSpinMeanSq (n + 1) tail)) x ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapRadiusTrace n d e duration pre tail ha) x ≤ M / ((n + 1 : ℝ) * g) := by
  apply (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < n + 1) hg)).mpr
  have hmap : Measurable (fun z : FeatureIndex (n + 1) → ℝ => x + z) := measurable_const.add measurable_id
  have h := integral_mono (μ := Measure.pi fun k => gaussianReal 0 (q₀ k))
    (((physicalFiniteCapRadiusTrace_smooth n d e duration pre tail ha).const_mul ((n + 1 : ℝ) * g)).integrable_comp_measurable hmap)
    ((physicalFiniteCapFieldTrace_smooth n d e pre tail ha).integrable_comp_measurable hmap)
    (fun z => physicalFiniteCapRadiusTrace_le_fieldTrace n d e duration pre tail ha hslope (x + z))
  rw [integral_const_mul] at h
  have hcap := physicalFiniteCapFieldTrace_rooted_le_endpoint n d e q₀ pre tail ha hfield x hmean
  rw [mul_comm]
  exact h.trans hcap

end
end OAI.SKFluctuations.LaplaceWindowFormalization
