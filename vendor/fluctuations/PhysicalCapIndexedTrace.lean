module

public import PhysicalCapActualLaw

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalFiniteCapIndexedTrace (n d : ℕ) (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) :
    (durations : List ℝ≥0) → (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) →
      {a : ℝ} → OrderedSteps a (pre ++ tail) → (FeatureIndex (n + 1) → ℝ) → ℝ
  | [], _, _, _, _, _ => 0
  | _ :: _, [], _, _, _, _ => 0
  | w :: durations, (m, q) :: pre, tail, _, ha, x =>
      w * (∫ t in 0..1, physicalFilledSourceTraceExpectation (n + 1) d
        (physicalJointGaussianDriver (n + 1) d e q) (pre ++ tail) ha.2.2.2 ha.2.2.1 1 t x) +
      shiftedMean (Measure.pi fun k => gaussianReal 0 (q k)) m
        (gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1)) (pre ++ tail))
        (physicalFiniteCapIndexedTrace n d e durations pre tail ha.2.2.2) x

theorem physicalFiniteCapIndexedTrace_smooth (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) :
    BddSmooth 0 (physicalFiniteCapIndexedTrace n d e durations pre tail ha) := by
  induction pre generalizing a durations with
  | nil => cases durations <;> exact BddSmooth.const 0 0
  | cons st pre ih =>
    cases durations with
    | nil => exact BddSmooth.const 0 0
    | cons w durations =>
      rcases st with ⟨m, q⟩
      exact ((physicalFilledSourceTrace_integral_smooth (n + 1) d _ (pre ++ tail)
        ha.2.2.2 ha.2.2.1 1).const_mul w).add
          ((ih durations ha.2.2.2).shiftedMean
            (gaussianHierarchy_regular (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
              (pre ++ tail) ha.2.2.2 0)
            (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
              (pre ++ tail) ha.2.2.2 m q))

theorem physicalFiniteCapIndexedTrace_le_fieldTrace (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a g : ℝ}
    (ha : OrderedSteps a (pre ++ tail))
    (hslope : List.Forall₂ (fun (w : ℝ≥0) (st : GaussianStep (FeatureIndex (n + 1))) => g * (w : ℝ) ≤ st.2 (Sum.inl 0)) durations pre)
    (x : FeatureIndex (n + 1) → ℝ) :
    (n + 1 : ℝ) * g * physicalFiniteCapIndexedTrace n d e durations pre tail ha x ≤
      physicalFiniteCapFieldTrace n d e pre tail ha x := by
  induction hslope generalizing a x with
  | nil => simp [physicalFiniteCapIndexedTrace, physicalFiniteCapFieldTrace]
  | @cons w st durations pre hw hrest ih =>
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
      have hs := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (n + 1 : ℝ))
      nlinarith [mul_le_mul_of_nonneg_right hs hI]
    · rw [← shiftedMean_const_mul]
      exact shiftedMean_mono
        ((physicalFiniteCapIndexedTrace_smooth n d e durations pre tail ha.2.2.2).const_mul ((n + 1 : ℝ) * g))
        (physicalFiniteCapFieldTrace_smooth n d e pre tail ha.2.2.2)
        (ih ha.2.2.2)
        (gaussianHierarchy_integrable (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
          (pre ++ tail) ha.2.2.2 m q x)

theorem physicalFiniteCapIndexedTrace_rooted_le_endpoint (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (q₀ : FeatureIndex (n + 1) → ℝ≥0)
    (durations : List ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a g M : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (hg : 0 < g)
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w : ℝ≥0) (st : GaussianStep (FeatureIndex (n + 1))) => g * (w : ℝ) ≤ st.2 (Sum.inl 0)) durations pre)
    (x : FeatureIndex (n + 1) → ℝ)
    (hmean : zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (prefixTest pre (gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1)) tail)
        (physicalSpinMeanSq (n + 1) tail)) x ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapIndexedTrace n d e durations pre tail ha) x ≤ M / ((n + 1 : ℝ) * g) := by
  apply (le_div_iff₀ (mul_pos (by positivity : (0 : ℝ) < n + 1) hg)).mpr
  have hmap : Measurable (fun z : FeatureIndex (n + 1) → ℝ => x + z) := measurable_const.add measurable_id
  have h := integral_mono (μ := Measure.pi fun k => gaussianReal 0 (q₀ k))
    (((physicalFiniteCapIndexedTrace_smooth n d e durations pre tail ha).const_mul ((n + 1 : ℝ) * g)).integrable_comp_measurable hmap)
    ((physicalFiniteCapFieldTrace_smooth n d e pre tail ha).integrable_comp_measurable hmap)
    (fun z => physicalFiniteCapIndexedTrace_le_fieldTrace n d e durations pre tail ha hslope (x + z))
  rw [integral_const_mul] at h
  have hcap := physicalFiniteCapFieldTrace_rooted_le_endpoint n d e q₀ pre tail ha hfield x hmean
  rw [mul_comm]
  exact h.trans hcap

theorem physicalFiniteCapIndexedTrace_rooted_le_pathSecondMoment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (q₀ : FeatureIndex (n + 1) → ℝ≥0)
    (durations : List ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {g M : ℝ}
    (ha : OrderedSteps 0 (pre ++ tail)) (hg : 0 < g)
    (hfield : ∀ st ∈ pre, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w : ℝ≥0) (st : GaussianStep (FeatureIndex (n + 1))) => g * (w : ℝ) ≤ st.2 (Sum.inl 0)) durations pre)
    (hmean : physicalPathSecondMoment (n + 1) (pre ++ tail) q₀ pre.length ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapIndexedTrace n d e durations pre tail ha) 0 ≤ M / ((n + 1 : ℝ) * g) := by
  apply physicalFiniteCapIndexedTrace_rooted_le_endpoint n d e q₀ durations pre tail ha hg hfield hslope 0
  exact (physicalPrefixMeanSq_eq_pathSecondMoment (n + 1) pre tail ha q₀).le.trans hmean

theorem physicalFiniteCapIndexedTrace_ordering_congr (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (durations : List ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n + 1)))) {a b : ℝ}
    (ha : OrderedSteps a (pre ++ tail)) (hb : OrderedSteps b (pre ++ tail)) :
    physicalFiniteCapIndexedTrace n d e durations pre tail ha =
      physicalFiniteCapIndexedTrace n d e durations pre tail hb := by
  cases durations <;> cases pre <;> rfl

theorem physicalFiniteCapIndexedTrace_zero_prefix (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (durations : List ℝ≥0)
    (common mid tail : List (GaussianStep (FeatureIndex (n + 1)))) {a b : ℝ}
    (ha : OrderedSteps a ((common ++ mid) ++ tail))
    (hb : OrderedSteps b (mid ++ tail)) (x : FeatureIndex (n + 1) → ℝ) :
    physicalFiniteCapIndexedTrace n d e (List.replicate common.length 0 ++ durations)
      (common ++ mid) tail ha x =
      prefixTest common (gaussianHierarchy (uniformWeight (n + 1)) (finiteFeature (n + 1))
        (mid ++ tail)) (physicalFiniteCapIndexedTrace n d e durations mid tail hb) x := by
  induction common generalizing a x with
  | nil =>
    simpa only [List.length_nil, List.replicate_zero, List.nil_append, prefixTest] using
      congrFun (physicalFiniteCapIndexedTrace_ordering_congr n d e durations mid tail ha hb) x
  | cons st common ih =>
    rcases st with ⟨m, q⟩
    simp only [List.length_cons, List.replicate_succ, List.cons_append,
      physicalFiniteCapIndexedTrace, NNReal.coe_zero, zero_mul, zero_add]
    rw [funext (ih ha.2.2.2)]
    simp only [prefixTest, prefixContinuation_hierarchy, List.append_assoc]

theorem physicalFiniteCapIndexedTrace_zero_prefix_rooted (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (q₀ : FeatureIndex (n + 1) → ℝ≥0)
    (durations : List ℝ≥0) (common mid tail : List (GaussianStep (FeatureIndex (n + 1))))
    (ha : OrderedSteps 0 ((common ++ mid) ++ tail)) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapIndexedTrace n d e (List.replicate common.length 0 ++ durations)
        (common ++ mid) tail ha) 0 =
      ∫ p, physicalFiniteCapIndexedTrace n d e durations mid tail
        ((by simpa only [List.append_assoc] using ha : OrderedSteps 0 (common ++ (mid ++ tail))).suffix common (mid ++ tail))
        (actualCutField (S := Spin (n + 1)) common (mid ++ tail) p.1 p.2)
        ∂rootedHierarchyPathLaw (uniformWeight (n + 1)) (finiteFeature (n + 1)) q₀ (common ++ (mid ++ tail)) := by
  let hfull : OrderedSteps 0 (common ++ (mid ++ tail)) := by
    simpa only [List.append_assoc] using ha
  let hmid := hfull.suffix common (mid ++ tail)
  rw [funext (physicalFiniteCapIndexedTrace_zero_prefix n d e durations common mid tail ha hmid)]
  exact physicalPrefixTest_eq_rootedCutExpectation (n + 1) common (mid ++ tail) hfull q₀
    (physicalFiniteCapIndexedTrace n d e durations mid tail hmid)
    (physicalFiniteCapIndexedTrace_smooth n d e durations mid tail hmid)

theorem physicalFiniteCapIndexedTrace_band_rooted_le_pathSecondMoment (n d : ℕ)
    (e : Fin (d + 1) ≃ FeatureIndex (n + 1)) (q₀ : FeatureIndex (n + 1) → ℝ≥0)
    (durations : List ℝ≥0) (common mid tail : List (GaussianStep (FeatureIndex (n + 1)))) {g M : ℝ}
    (ha : OrderedSteps 0 ((common ++ mid) ++ tail)) (hg : 0 < g)
    (hfield : ∀ st ∈ common ++ mid, ∀ j, st.2 (Sum.inl j) = st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w : ℝ≥0) (st : GaussianStep (FeatureIndex (n + 1))) =>
      g * (w : ℝ) ≤ st.2 (Sum.inl 0)) durations mid)
    (hmean : physicalPathSecondMoment (n + 1) ((common ++ mid) ++ tail) q₀ (common ++ mid).length ≤ M) :
    zeroContinuation (Measure.pi fun k => gaussianReal 0 (q₀ k))
      (physicalFiniteCapIndexedTrace n d e (List.replicate common.length 0 ++ durations)
        (common ++ mid) tail ha) 0 ≤ M / ((n + 1 : ℝ) * g) := by
  have hzero : List.Forall₂ (fun (w : ℝ≥0) (st : GaussianStep (FeatureIndex (n + 1))) =>
      g * (w : ℝ) ≤ st.2 (Sum.inl 0)) (List.replicate common.length 0) common := by
    clear ha hfield hmean
    induction common with
    | nil => exact List.Forall₂.nil
    | cons st common ih =>
      simp only [List.length_cons, List.replicate_succ]
      exact List.Forall₂.cons (by simp) ih
  exact physicalFiniteCapIndexedTrace_rooted_le_pathSecondMoment n d e q₀
    (List.replicate common.length 0 ++ durations) (common ++ mid) tail ha hg hfield
    (List.rel_append hzero hslope) hmean

end
end OAI.SKFluctuations.LaplaceWindowFormalization
