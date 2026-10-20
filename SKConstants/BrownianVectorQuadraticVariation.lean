module
public import SKConstants.BrownianVectorContinuousIntegral
public import SKConstants.BrownianQuadraticVariation

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianVectorContinuousCoordinateQuadraticVariation {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ) (idx : ι)
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (T : ℝ≥0) (u : A × (ι → Ω)) : ℝ :=
  ∫ s in (0 : ℝ)..T,brownianVectorContinuousCoordinateCoefficient D idx H s.toNNReal u ^ 2

lemma brownianVectorContinuousCoordinateVariation_tendsto_path {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ) (idx : ι)
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (G : ScalarDyadicNestedGrid) (k : ℕ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l)
    (u : A × (ι → Ω)) (hc : Continuous (fun s => brownianVectorContinuousCoordinateCoefficient D idx H s u)) :
    Tendsto (fun l => brownianVectorCoordinatePredictableVariation D idx (G.time l)
      (brownianVectorContinuousCoordinateMeshCoefficient H (G.time l)) (k*2^l) u) atTop
      (𝓝 (brownianVectorContinuousCoordinateQuadraticVariation D idx H (G.time 0 k) u)) := by
  have hcont : Continuous (fun s : ℝ => brownianVectorContinuousCoordinateCoefficient D idx H s.toNNReal u ^ 2) :=
    (hc.comp continuous_real_toNNReal).pow 2
  have ht := continuous_left_quadrature_tendsto _ hcont (G.time 0 k) G k rfl δ hδ hwidth
  simp only [Real.toNNReal_coe] at ht
  simpa only [brownianVectorCoordinatePredictableVariation,predictableGaussianVariation_eq_range_sum,
    brownianVectorCoordinateCoefficient,brownianVectorContinuousCoordinateMeshCoefficient,brownianVectorContinuousCoordinateCoefficient,
    Real.toNNReal_coe,brownianVectorContinuousCoordinateQuadraticVariation] using ht

lemma brownianVectorContinuousCoordinateVariation_le {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ) (idx : ι)
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) (u : A × (ι → Ω)) :
    brownianVectorCoordinatePredictableVariation D idx (G.time l)
      (brownianVectorContinuousCoordinateMeshCoefficient H (G.time l)) (k*2^l) u ≤ C^2*(G.time 0 k : ℝ) := by
  rw [brownianVectorCoordinatePredictableVariation,predictableGaussianVariation_eq_range_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (k*2^l),C^2*(brownianMeshVariance (G.time l) i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
      exact (show H (G.time l i) (u.1,brownianVectorFullPast D (G.time l i) u.2)^2 ≤ C^2 from by
        simpa only [Real.norm_eq_abs,sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (hC (G.time l i) _) 2)
    _ = _ := by rw [← Finset.mul_sum,G.variance_sum]

lemma brownianVectorContinuousCoordinateQuadraticVariation_bounds {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ) (idx : ι)
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (T : ℝ≥0) (u : A × (ι → Ω)) :
    0 ≤ brownianVectorContinuousCoordinateQuadraticVariation D idx H T u ∧
      brownianVectorContinuousCoordinateQuadraticVariation D idx H T u ≤ C^2*(T : ℝ) := by
  constructor
  · exact intervalIntegral.integral_nonneg T.coe_nonneg (fun s hs => sq_nonneg _)
  · have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
      (f := fun s => brownianVectorContinuousCoordinateCoefficient D idx H s.toNNReal u ^ 2) (C := C^2)
      (fun s hs => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC s.toNNReal _) 2)
    simp only [sub_zero,abs_of_nonneg T.coe_nonneg,Real.norm_eq_abs] at hb
    exact (le_abs_self _).trans hb

theorem brownianVectorContinuousCoordinateVariation_tendsto_L2 {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (idx : ι) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousCoordinatePastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)), Continuous (fun s => brownianVectorContinuousCoordinateCoefficient D idx H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    AEStronglyMeasurable (brownianVectorContinuousCoordinateQuadraticVariation D idx H (G.time 0 k)) (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      (∀ l, Integrable (fun u => (brownianVectorCoordinatePredictableVariation D idx (G.time l)
        (brownianVectorContinuousCoordinateMeshCoefficient H (G.time l)) (k*2^l) u-
          brownianVectorContinuousCoordinateQuadraticVariation D idx H (G.time 0 k) u)^2) (P.prod (Measure.pi (fun _ : ι => Q)))) ∧
      Tendsto (fun l => ∫ u, (brownianVectorCoordinatePredictableVariation D idx (G.time l)
        (brownianVectorContinuousCoordinateMeshCoefficient H (G.time l)) (k*2^l) u-
          brownianVectorContinuousCoordinateQuadraticVariation D idx H (G.time 0 k) u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q))) atTop (𝓝 0) := by
  let V := C^2*(G.time 0 k : ℝ)
  let F : ℕ → A × (ι → Ω) → ℝ := fun l => brownianVectorCoordinatePredictableVariation D idx (G.time l)
    (brownianVectorContinuousCoordinateMeshCoefficient H (G.time l)) (k*2^l)
  let Y : A × (ι → Ω) → ℝ := brownianVectorContinuousCoordinateQuadraticVariation D idx H (G.time 0 k)
  have hm (l : ℕ) : AEStronglyMeasurable (F l) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    (aemeasurable_predictableGaussianVariation (P.prod (Measure.pi (fun _ : ι => Q))) _ _
      (aemeasurable_brownianVectorCoordinateCoefficient P Q D idx hD hmD _ _ (fun i => hH _) ) _).aestronglyMeasurable
  have hpath : ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)), Tendsto (fun l => F l u) atTop (𝓝 (Y u)) := by
    filter_upwards [hc] with u hu
    exact brownianVectorContinuousCoordinateVariation_tendsto_path D idx H G k δ hδ hwidth u hu
  have hYm : AEStronglyMeasurable Y (P.prod (Measure.pi (fun _ : ι => Q))) := aestronglyMeasurable_of_tendsto_ae atTop hm hpath
  have hbound (l : ℕ) (u : A × (ι → Ω)) : ‖(F l u-Y u)^2‖ ≤ V^2 := by
    have hF0 : 0 ≤ F l u := predictableGaussianVariation_nonneg _ _ _ _
    have hF := brownianVectorContinuousCoordinateVariation_le D idx H C hC G k l u
    have hY := brownianVectorContinuousCoordinateQuadraticVariation_bounds D idx H C hC (G.time 0 k) u
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change _ ≤ V at hF
    change 0 ≤ Y u ∧ Y u ≤ V at hY
    have hab : |F l u-Y u| ≤ V := abs_le.mpr ⟨by linarith [hY.1,hY.2],by linarith [hY.1,hY.2]⟩
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
  have hi (l : ℕ) : Integrable (fun u => (F l u-Y u)^2) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    (integrable_const (V^2 : ℝ)).mono' (((hm l).sub hYm).pow 2) (ae_of_all _ (hbound l))
  refine ⟨hYm,hi,?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := P.prod (Measure.pi (fun _ : ι => Q))) (bound := fun _ => V^2)
    (fun l => ((hm l).sub hYm).pow 2) (integrable_const _) (fun l => ae_of_all _ (hbound l)) (by
      filter_upwards [hpath] with u hu
      simpa only [Pi.pow_apply,Pi.sub_apply,sub_self,zero_pow (by norm_num : 2 ≠ 0)] using (hu.sub_const (Y u)).pow 2)
  simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero,F,Y] using ht

def brownianVectorContinuousQuadraticVariation {A ι Ω : Type*} [Fintype ι]
    (D : ℝ≥0 → Ω → ℝ) (H : BrownianVectorContinuousPastCoefficient A ι)
    (T : ℝ≥0) (u : A × (ι → Ω)) : ℝ :=
  ∑ i,brownianVectorContinuousCoordinateQuadraticVariation D i (fun s u => H s u i) T u

lemma brownianVectorPredictableVariation_eq_sum_coordinate {A ι Ω : Type*} [Fintype ι]
    (D : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (H : BrownianVectorPredictableCoefficient A ι t) (n : ℕ) (u : A × (ι → Ω)) :
    brownianVectorPredictableVariation D t H n u = ∑ i,
      brownianVectorCoordinatePredictableVariation D i t (fun k u => H k u i) n u := by
  rw [brownianVectorPredictableVariation,predictableGaussianVectorVariation_eq_fin_sum]
  simp_rw [brownianVectorCoordinatePredictableVariation,predictableGaussianVariation_eq_fin_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma brownianVectorContinuousVariation_le {A ι Ω : Type*} [Fintype ι]
    (D : ℝ≥0 → Ω → ℝ) (H : BrownianVectorContinuousPastCoefficient A ι)
    (C : ℝ) (hC : ∀ s u i, ‖H s u i‖ ≤ C)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) (u : A × (ι → Ω)) :
    brownianVectorPredictableVariation D (G.time l)
      (brownianVectorContinuousMeshCoefficient H (G.time l)) (k*2^l) u ≤
        (Fintype.card ι : ℝ)*C^2*(G.time 0 k : ℝ) := by
  rw [brownianVectorPredictableVariation_eq_sum_coordinate]
  calc
    _ ≤ ∑ i : ι,C^2*(G.time 0 k : ℝ) := Finset.sum_le_sum (fun i _ =>
      brownianVectorContinuousCoordinateVariation_le D i (fun s u => H s u i) C
        (fun s u => hC s u i) G k l u)
    _ = _ := by simp [mul_assoc]

lemma brownianVectorContinuousQuadraticVariation_bounds {A ι Ω : Type*} [Fintype ι]
    (D : ℝ≥0 → Ω → ℝ) (H : BrownianVectorContinuousPastCoefficient A ι)
    (C : ℝ) (hC : ∀ s u i, ‖H s u i‖ ≤ C) (T : ℝ≥0) (u : A × (ι → Ω)) :
    0 ≤ brownianVectorContinuousQuadraticVariation D H T u ∧
      brownianVectorContinuousQuadraticVariation D H T u ≤ (Fintype.card ι : ℝ)*C^2*(T : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => (brownianVectorContinuousCoordinateQuadraticVariation_bounds
      D i (fun s u => H s u i) C (fun s u => hC s u i) T u).1)
  · calc
      _ ≤ ∑ i : ι,C^2*(T : ℝ) := Finset.sum_le_sum (fun i _ =>
        (brownianVectorContinuousCoordinateQuadraticVariation_bounds D i (fun s u => H s u i)
          C (fun s u => hC s u i) T u).2)
      _ = _ := by simp [mul_assoc]

theorem brownianVectorContinuousVariation_tendsto_L2 {A ι Ω : Type*}
    [MeasurableSpace A] [Fintype ι] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousPastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u i, ‖H s u i‖ ≤ C)
    (hc : ∀ i, ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)),
      Continuous (fun s => brownianVectorContinuousCoefficient D H s u i))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    AEStronglyMeasurable (brownianVectorContinuousQuadraticVariation D H (G.time 0 k))
      (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      (∀ l, Integrable (fun u => (brownianVectorPredictableVariation D (G.time l)
        (brownianVectorContinuousMeshCoefficient H (G.time l)) (k*2^l) u-
          brownianVectorContinuousQuadraticVariation D H (G.time 0 k) u)^2)
        (P.prod (Measure.pi (fun _ : ι => Q)))) ∧
      Tendsto (fun l => ∫ u, (brownianVectorPredictableVariation D (G.time l)
        (brownianVectorContinuousMeshCoefficient H (G.time l)) (k*2^l) u-
          brownianVectorContinuousQuadraticVariation D H (G.time 0 k) u)^2
        ∂P.prod (Measure.pi (fun _ : ι => Q))) atTop (𝓝 0) := by
  have h (i : ι) := brownianVectorContinuousCoordinateVariation_tendsto_L2 P Q D i hD hmD
    (fun s u => H s u i) (fun s => (measurable_pi_apply i).comp (hH s)) C
      (fun s u => hC s u i) (hc i) G k δ hδ hwidth
  have hm (i : ι) (l : ℕ) : AEStronglyMeasurable
      (brownianVectorCoordinatePredictableVariation D i (G.time l)
        (fun j u => H (G.time l j) u i) (k*2^l)) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    (aemeasurable_predictableGaussianVariation _ _ _
      (aemeasurable_brownianVectorCoordinateCoefficient P Q D i hD hmD _ _
        (fun j => (measurable_pi_apply i).comp (hH _))) _).aestronglyMeasurable
  refine ⟨?_,?_,?_⟩
  · convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (h i).1) using 1
    funext u
    simp only [brownianVectorContinuousQuadraticVariation,Finset.sum_apply]
  · intro l
    simp_rw [brownianVectorPredictableVariation_eq_sum_coordinate,
      brownianVectorContinuousQuadraticVariation,← Finset.sum_sub_distrib]
    exact integrable_sq_finset_sum Finset.univ
      (fun i _ => ((hm i l).sub (h i).1).aemeasurable) (fun i _ => (h i).2.1 l)
  · simp_rw [brownianVectorPredictableVariation_eq_sum_coordinate,
      brownianVectorContinuousQuadraticVariation,← Finset.sum_sub_distrib]
    exact tendsto_integral_sq_finset_sum Finset.univ
      (fun i _ l => ((hm i l).sub (h i).1).aemeasurable)
      (fun i _ l => (h i).2.1 l) (fun i _ => (h i).2.2)

end SKConstants
