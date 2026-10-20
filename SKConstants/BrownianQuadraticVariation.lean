module
public import SKConstants.BrownianContinuousLikelihood

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

lemma continuous_left_quadrature_interval_error (f : ℝ → ℝ) (hf : Continuous f)
    {a b η : ℝ} (hab : a ≤ b) (hη : ∀ s ∈ Icc a b, |f a-f s| ≤ η) :
    |f a*(b-a)-(∫ s in a..b,f s)| ≤ η*(b-a) := by
  have he : f a*(b-a)-(∫ s in a..b,f s) = ∫ s in a..b,f a-f s := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable a b),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun s => f a-f s) (C := η) (fun s hs => by
      rw [uIoc_of_le hab] at hs
      simpa only [Real.norm_eq_abs] using hη s ⟨hs.1.le,hs.2⟩)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hb

theorem continuous_left_quadrature_tendsto (f : ℝ → ℝ) (hf : Continuous f)
    (T : ℝ≥0) (G : ScalarDyadicNestedGrid) (k : ℕ) (hT : G.time 0 k = T)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l →
      (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    Tendsto (fun l => ∑ i ∈ Finset.range (k*2^l),f (G.time l i)*
      (brownianMeshVariance (G.time l) i : ℝ)) atTop (𝓝 (∫ s in (0 : ℝ)..T,f s)) := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε/((T : ℝ)+1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hu : UniformContinuousOn f (Icc 0 (T : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨d,hd,hUC⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hd))
  refine ⟨N,fun l hl => ?_⟩
  let a : ℕ → ℝ := fun i => G.time l i
  have ha (i : ℕ) : a i ≤ a (i+1) := by exact_mod_cast G.monotone l (by omega : i ≤ i+1)
  have hm (i : ℕ) : (brownianMeshVariance (G.time l) i : ℝ) = a (i+1)-a i := by
    rw [brownianMeshVariance,NNReal.coe_sub (G.monotone l (by omega))]
  have he : (∑ i∈Finset.range (k*2^l),f (a i)*(a (i+1)-a i))-(∫ s in (0 : ℝ)..T,f s) =
      ∑ i∈Finset.range (k*2^l),(f (a i)*(a (i+1)-a i)-(∫ s in a i..a (i+1),f s)) := by
    rw [Finset.sum_sub_distrib,intervalIntegral.sum_integral_adjacent_intervals
      (fun i hi => hf.intervalIntegrable _ _)]
    simp only [a,G.zero,G.duration,hT,NNReal.coe_zero]
  have hbound : |(∑ i∈Finset.range (k*2^l),f (a i)*(a (i+1)-a i))-
      (∫ s in (0 : ℝ)..T,f s)| ≤ η*(T : ℝ) := by
    rw [he]
    calc
      _ ≤ ∑ i∈Finset.range (k*2^l),|f (a i)*(a (i+1)-a i)-(∫ s in a i..a (i+1),f s)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i∈Finset.range (k*2^l),η*(a (i+1)-a i) := by
        apply Finset.sum_le_sum
        intro i hi
        apply continuous_left_quadrature_interval_error f hf (ha i)
        intro s hs
        have hai : a i ∈ Icc 0 (T : ℝ) :=
          ⟨NNReal.coe_nonneg _,by exact_mod_cast (G.le_duration (Finset.mem_range.mp hi).le).trans_eq hT⟩
        have hiN : i < k*2^l := Finset.mem_range.mp hi
        have hai1 : a (i+1) ≤ T := by
          exact_mod_cast (G.le_duration (by omega : i+1 ≤ k*2^l)).trans_eq hT
        have hsT : s ∈ Icc 0 (T : ℝ) := ⟨hai.1.trans hs.1,hs.2.trans hai1⟩
        have hdist : dist (a i) s < d := by
          rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hs.1)]
          exact (sub_le_sub_right hs.2 _).trans_lt ((hwidth l i (Finset.mem_range.mp hi)).trans_lt (hN l hl))
        exact (show |f (a i)-f s| < η by simpa only [Real.dist_eq] using hUC _ hai _ hsT hdist).le
      _ = η*(T : ℝ) := by
        rw [← Finset.mul_sum,Finset.sum_range_sub]
        simp only [a,G.zero,G.duration,hT,NNReal.coe_zero,sub_zero]
  have hηT : η*(T : ℝ) < ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < (T : ℝ)+1)).mpr
    nlinarith
  rw [Real.dist_eq]
  simp_rw [hm]
  exact hbound.trans_lt hηT

def brownianContinuousQuadraticVariation {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (T : ℝ≥0) (u : A × Ω) : ℝ :=
  ∫ s in (0 : ℝ)..T,brownianContinuousCoefficient D H s.toNNReal u ^ 2

lemma brownianContinuousVariation_tendsto_path {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (G : ScalarDyadicNestedGrid) (k : ℕ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l)
    (u : A × Ω) (hc : Continuous (fun s => brownianContinuousCoefficient D H s u)) :
    Tendsto (fun l => brownianStaticPredictableVariation D (G.time l)
      (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l) u) atTop
      (𝓝 (brownianContinuousQuadraticVariation D H (G.time 0 k) u)) := by
  have hcont : Continuous (fun s : ℝ => brownianContinuousCoefficient D H s.toNNReal u ^ 2) :=
    (hc.comp continuous_real_toNNReal).pow 2
  have ht := continuous_left_quadrature_tendsto _ hcont (G.time 0 k) G k rfl δ hδ hwidth
  simp only [Real.toNNReal_coe] at ht
  simpa only [brownianStaticPredictableVariation,predictableGaussianVariation_eq_range_sum,
    brownianStaticCoefficient,brownianContinuousMeshCoefficient,brownianContinuousCoefficient,
    Real.toNNReal_coe,brownianContinuousQuadraticVariation] using ht

lemma brownianContinuousVariation_le {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) (u : A × Ω) :
    brownianStaticPredictableVariation D (G.time l)
      (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l) u ≤ C^2*(G.time 0 k : ℝ) := by
  rw [brownianStaticPredictableVariation,predictableGaussianVariation_eq_range_sum]
  calc
    _ ≤ ∑ i ∈ Finset.range (k*2^l),C^2*(brownianMeshVariance (G.time l) i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
      exact (show H (G.time l i) (u.1,brownianFullPast D (G.time l i) u.2)^2 ≤ C^2 from by
        simpa only [Real.norm_eq_abs,sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (hC (G.time l i) _) 2)
    _ = _ := by rw [← Finset.mul_sum,G.variance_sum]

lemma brownianContinuousQuadraticVariation_bounds {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (T : ℝ≥0) (u : A × Ω) :
    0 ≤ brownianContinuousQuadraticVariation D H T u ∧
      brownianContinuousQuadraticVariation D H T u ≤ C^2*(T : ℝ) := by
  constructor
  · exact intervalIntegral.integral_nonneg T.coe_nonneg (fun s hs => sq_nonneg _)
  · have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
      (f := fun s => brownianContinuousCoefficient D H s.toNNReal u ^ 2) (C := C^2)
      (fun s hs => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC s.toNNReal _) 2)
    simp only [sub_zero,abs_of_nonneg T.coe_nonneg,Real.norm_eq_abs] at hb
    exact (le_abs_self _).trans hb

theorem brownianContinuousVariation_tendsto_L2 {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod Q, Continuous (fun s => brownianContinuousCoefficient D H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    AEStronglyMeasurable (brownianContinuousQuadraticVariation D H (G.time 0 k)) (P.prod Q) ∧
      (∀ l, Integrable (fun u => (brownianStaticPredictableVariation D (G.time l)
        (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l) u-
          brownianContinuousQuadraticVariation D H (G.time 0 k) u)^2) (P.prod Q)) ∧
      Tendsto (fun l => ∫ u, (brownianStaticPredictableVariation D (G.time l)
        (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l) u-
          brownianContinuousQuadraticVariation D H (G.time 0 k) u)^2 ∂P.prod Q) atTop (𝓝 0) := by
  let V := C^2*(G.time 0 k : ℝ)
  let F : ℕ → A × Ω → ℝ := fun l => brownianStaticPredictableVariation D (G.time l)
    (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l)
  let Y : A × Ω → ℝ := brownianContinuousQuadraticVariation D H (G.time 0 k)
  have hm (l : ℕ) : AEStronglyMeasurable (F l) (P.prod Q) :=
    (aemeasurable_predictableGaussianVariation (P.prod Q) _ _
      (aemeasurable_brownianStaticCoefficient P Q D hD hmD _ _ (fun i => hH _) ) _).aestronglyMeasurable
  have hpath : ∀ᵐ u ∂P.prod Q, Tendsto (fun l => F l u) atTop (𝓝 (Y u)) := by
    filter_upwards [hc] with u hu
    exact brownianContinuousVariation_tendsto_path D H G k δ hδ hwidth u hu
  have hYm : AEStronglyMeasurable Y (P.prod Q) := aestronglyMeasurable_of_tendsto_ae atTop hm hpath
  have hbound (l : ℕ) (u : A × Ω) : ‖(F l u-Y u)^2‖ ≤ V^2 := by
    have hF0 : 0 ≤ F l u := predictableGaussianVariation_nonneg _ _ _ _
    have hF := brownianContinuousVariation_le D H C hC G k l u
    have hY := brownianContinuousQuadraticVariation_bounds D H C hC (G.time 0 k) u
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    change _ ≤ V at hF
    change 0 ≤ Y u ∧ Y u ≤ V at hY
    have hab : |F l u-Y u| ≤ V := abs_le.mpr ⟨by linarith [hY.1,hY.2],by linarith [hY.1,hY.2]⟩
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
  have hi (l : ℕ) : Integrable (fun u => (F l u-Y u)^2) (P.prod Q) :=
    (integrable_const (V^2 : ℝ)).mono' (((hm l).sub hYm).pow 2) (ae_of_all _ (hbound l))
  refine ⟨hYm,hi,?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := P.prod Q) (bound := fun _ => V^2)
    (fun l => ((hm l).sub hYm).pow 2) (integrable_const _) (fun l => ae_of_all _ (hbound l)) (by
      filter_upwards [hpath] with u hu
      simpa only [Pi.pow_apply,Pi.sub_apply,sub_self,zero_pow (by norm_num : 2 ≠ 0)] using (hu.sub_const (Y u)).pow 2)
  simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero,F,Y] using ht

end SKConstants
