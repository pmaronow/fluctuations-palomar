module

public import PhysicalBoundaryFilledTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalBoundarySourceTrace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (x : FeatureIndex n → ℝ) : ℝ :=
  ∑ i, ∑ j, (hierarchySourceHessianMatrix (uniformWeight n) (finiteFeature n)
    (physicalNormalizedSourceMap n) steps x i j)^2

theorem physicalBoundarySourceTrace_smooth (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps) :
    BddSmooth 0 (physicalBoundarySourceTrace n steps) := by
  apply BddSmooth.sum Finset.univ
  intro i _
  apply BddSmooth.sum Finset.univ
  intro j _
  simpa only [physicalSourceHessian_eq_response, pow_two] using
    (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1))
      steps ha 0).mul
    (gaussianHierarchyResponse_smooth (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) (physicalNormalizedSourceMap n (Pi.single j 1))
      steps ha 0)

def physicalFiniteCapBoundaryTrace (n : ℕ) :
    (durations : List ℝ≥0) → (pre tail : List (GaussianStep (FeatureIndex n))) →
      {a : ℝ} → OrderedSteps a (pre ++ tail) → (FeatureIndex n → ℝ) → ℝ
  | [], _, _, _, _, _ => 0
  | _::_, [], _, _, _, _ => 0
  | w::duration, (m,q)::pre, tail, _, ha, x =>
      w*physicalBoundarySourceTrace n (((m,q)::pre) ++ tail) x +
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
        (gaussianHierarchy (uniformWeight n) (finiteFeature n) (pre ++ tail))
        (physicalFiniteCapBoundaryTrace n duration pre tail ha.2.2.2) x

theorem physicalFiniteCapBoundaryTrace_smooth (n : ℕ) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) :
    BddSmooth 0 (physicalFiniteCapBoundaryTrace n durations pre tail ha) := by
  induction pre generalizing a durations with
  | nil => cases durations <;> exact BddSmooth.const 0 0
  | cons st pre ih =>
    cases durations with
    | nil => exact BddSmooth.const 0 0
    | cons w duration =>
      rcases st with ⟨m,q⟩
      exact ((physicalBoundarySourceTrace_smooth n (((m,q)::pre) ++ tail) ha).const_mul w).add
        ((ih duration ha.2.2.2).shiftedMean
          (gaussianHierarchy_regular (uniformWeight_pos n) (finiteFeature n) (pre ++ tail) ha.2.2.2 0)
          (gaussianHierarchy_integrable (uniformWeight_pos n) (finiteFeature n) (pre ++ tail) ha.2.2.2 m q))

theorem physicalFiniteCapBoundaryTrace_le_indexedTrace (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a mesh : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ w ∈ durations, (w:ℝ) ≤ mesh) (x : FeatureIndex (n+1) → ℝ) :
    physicalFiniteCapBoundaryTrace (n+1) durations pre tail ha x ≤
      2*physicalFiniteCapIndexedTrace n d e durations pre tail ha x +
      2*mesh*physicalFiniteCapEnergy (n+1) d e pre tail ha x := by
  induction pre generalizing a durations x with
  | nil => cases durations <;> simp [physicalFiniteCapBoundaryTrace,physicalFiniteCapIndexedTrace,physicalFiniteCapEnergy]
  | cons st pre ih =>
    cases durations with
    | nil =>
      simp only [physicalFiniteCapBoundaryTrace,physicalFiniteCapIndexedTrace,mul_zero,zero_add]
      exact mul_nonneg (by positivity) (physicalFiniteCapEnergy_nonneg (n+1) d e (st::pre) tail ha x)
    | cons w durations =>
      rcases st with ⟨m,q⟩
      have hi := gaussianHierarchy_integrable (uniformWeight_pos (n+1)) (finiteFeature (n+1))
        (pre++tail) ha.2.2.2 m q x
      have hE : 0 ≤ ∫ t in 0..1, physicalFilledOverlapEnergy (n+1) d
          (physicalJointGaussianDriver (n+1) d e q) (pre++tail) ha.2.2.2 ha.2.2.1 1 t x := by
        apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
        intro t _
        exact physicalFilledOverlapEnergy_nonneg (n+1) d _ (pre++tail) ha.2.2.2 ha.2.2.1 1 t x
      have hm2 : m^2 ≤ 1 := by
        have hb := OrderedSteps.bounds ha.2.2.2
        nlinarith [hb.1,hb.2]
      have hw := hmesh w (by simp)
      have hwm : (w:ℝ)*m^2 ≤ mesh :=
        (mul_le_mul_of_nonneg_left hm2 w.coe_nonneg).trans (by simpa using hw)
      have hpoint := physicalBoundaryTrace_le_filledTrace_and_energy (n+1) d e q
        (pre++tail) ha.2.2.2 ha.2.2.1 x
      have hhead : (w:ℝ)*physicalBoundarySourceTrace (n+1) (((m,q)::pre)++tail) x ≤
          2*((w:ℝ)*(∫ t in 0..1, physicalFilledSourceTraceExpectation (n+1) d
            (physicalJointGaussianDriver (n+1) d e q) (pre++tail) ha.2.2.2 ha.2.2.1 1 t x)) +
          2*mesh*(∫ t in 0..1, physicalFilledOverlapEnergy (n+1) d
            (physicalJointGaussianDriver (n+1) d e q) (pre++tail) ha.2.2.2 ha.2.2.1 1 t x) := by
        have hp := mul_le_mul_of_nonneg_left hpoint w.coe_nonneg
        have he := mul_le_mul_of_nonneg_right hwm hE
        change (w:ℝ)*physicalBoundarySourceTrace (n+1) (((m,q)::pre)++tail) x ≤ _ at hp
        nlinarith
      have htail := shiftedMean_mono
        (physicalFiniteCapBoundaryTrace_smooth (n+1) durations pre tail ha.2.2.2)
        (((physicalFiniteCapIndexedTrace_smooth n d e durations pre tail ha.2.2.2).const_mul 2).add
          ((physicalFiniteCapEnergy_smooth (n+1) d e pre tail ha.2.2.2).const_mul (2*mesh)))
        (ih durations ha.2.2.2 (fun w hw => hmesh w (by simp only [List.mem_cons]; exact Or.inr hw))) hi
      rw [shiftedMean_add
        ((physicalFiniteCapIndexedTrace_smooth n d e durations pre tail ha.2.2.2).const_mul 2)
        ((physicalFiniteCapEnergy_smooth (n+1) d e pre tail ha.2.2.2).const_mul (2*mesh)) hi,
        shiftedMean_const_mul, shiftedMean_const_mul] at htail
      simp only [physicalFiniteCapBoundaryTrace,physicalFiniteCapIndexedTrace,physicalFiniteCapEnergy]
      nlinarith

theorem physicalFiniteCapBoundaryTrace_rooted_le_endpoint (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1) → ℝ≥0)
    (durations : List ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n+1))))
    {a mesh g M : ℝ} (ha : OrderedSteps a (pre++tail)) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ w ∈ durations, (w:ℝ) ≤ mesh) (hg : 0 < g)
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) durations pre) (x : FeatureIndex (n+1) → ℝ)
    (hmean : zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (prefixTest pre (gaussianHierarchy (uniformWeight (n+1)) (finiteFeature (n+1)) tail)
        (physicalSpinMeanSq (n+1) tail)) x ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapBoundaryTrace (n+1) durations pre tail ha) x ≤
      2*M/((n+1:ℝ)*g) + 2*mesh*M := by
  have hmap : Measurable (fun z : FeatureIndex (n+1) → ℝ => x+z) :=
    measurable_const.add measurable_id
  have hCap := physicalFiniteCapIndexedTrace_smooth n d e durations pre tail ha
  have hEnergy := physicalFiniteCapEnergy_smooth (n+1) d e pre tail ha
  have hiCap : Integrable (fun z => 2*physicalFiniteCapIndexedTrace n d e durations pre tail ha (x+z))
      (Measure.pi fun k => gaussianReal 0 (q₀ k)) :=
    (hCap.const_mul 2).integrable_comp_measurable hmap
  have hiEnergy : Integrable (fun z => 2*mesh*physicalFiniteCapEnergy (n+1) d e pre tail ha (x+z))
      (Measure.pi fun k => gaussianReal 0 (q₀ k)) :=
    (hEnergy.const_mul (2*mesh)).integrable_comp_measurable hmap
  have h := integral_mono (μ := Measure.pi fun k => gaussianReal 0 (q₀ k))
    ((physicalFiniteCapBoundaryTrace_smooth (n+1) durations pre tail ha).integrable_comp_measurable hmap)
    (((hCap.const_mul 2).add (hEnergy.const_mul (2*mesh))).integrable_comp_measurable hmap)
    (fun z => physicalFiniteCapBoundaryTrace_le_indexedTrace n d e durations pre tail ha
      hmesh0 hmesh (x+z))
  rw [integral_add hiCap hiEnergy,integral_const_mul,integral_const_mul] at h
  have hcap := physicalFiniteCapIndexedTrace_rooted_le_endpoint n d e q₀ durations pre tail ha
    hg hfield hslope x hmean
  have he := physicalFiniteCapEnergy_rooted_le_endpoint (n+1) d e q₀ pre tail ha x hmean
  change _ ≤ 2*zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapIndexedTrace n d e durations pre tail ha) x +
    2*mesh*zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapEnergy (n+1) d e pre tail ha) x at h
  calc
    _ ≤ _ := h
    _ ≤ 2*(M/((n+1:ℝ)*g))+2*mesh*M :=
      add_le_add (mul_le_mul_of_nonneg_left hcap (by norm_num))
        (mul_le_mul_of_nonneg_left he (by positivity))
    _ = _ := by ring

theorem physicalFiniteCapBoundaryTrace_rooted_le_pathSecondMoment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1) → ℝ≥0)
    (durations : List ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n+1))))
    {mesh g M : ℝ} (ha : OrderedSteps 0 (pre++tail)) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ w ∈ durations, (w:ℝ) ≤ mesh) (hg : 0 < g)
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) durations pre)
    (hmean : physicalPathSecondMoment (n+1) (pre++tail) q₀ pre.length ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapBoundaryTrace (n+1) durations pre tail ha) 0 ≤
      2*M/((n+1:ℝ)*g)+2*mesh*M := by
  apply physicalFiniteCapBoundaryTrace_rooted_le_endpoint n d e q₀ durations pre tail ha
    hmesh0 hmesh hg hfield hslope 0
  exact (physicalPrefixMeanSq_eq_pathSecondMoment (n+1) pre tail ha q₀).le.trans hmean

end OAI.SKFluctuations.LaplaceWindowFormalization
