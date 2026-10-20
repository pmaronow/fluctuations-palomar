module

public import SKConstants.Completion.LBase.CurvatureSums

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] BoundedLipschitzDrift.solution rawPastCurvature rawPastField actualCurvatureProcess
set_option maxHeartbeats 500000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma measurable_curvature_at (W : BrownianSystem Ω) (β r : ℝ) :
    Measurable (actualCurvatureProcess W β r) := by
  have hpair : Measurable (fun w : Ω => (r, w)) := measurable_const.prodMk measurable_id
  exact (measurable_actualCurvatureProcess W β).comp hpair

lemma curvature_time_integral_bound (W : BrownianSystem Ω) (β s t : ℝ) (w : Ω) :
    |∫ r in s..t, actualCurvatureProcess W β r w| ≤ |t - s| := by
  have hh : ‖∫ r in s..t, actualCurvatureProcess W β r w‖ ≤ 1 * |t - s| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
      (C := (1 : ℝ)) (fun r _ => by
        rw [Real.norm_eq_abs]
        exact actualCurvatureProcess_abs_le W β r w)
  rw [Real.norm_eq_abs, one_mul] at hh
  exact hh

lemma curvature_integrated_term_integrable (W : BrownianSystem Ω) (β : ℝ) (S T : ℝ≥0) :
    Integrable (fun w => actualCurvatureProcess W β S w *
      (∫ r in (S : ℝ)..T, actualCurvatureProcess W β r w)) W.law := by
  have hm := SKConstantsOAI.ZeroTemperatureSK.WeakIto.measurable_time_integral (Ω := Ω) (f := actualCurvatureProcess W β)
    (measurable_actualCurvatureProcess W β) S T
  have ha := measurable_curvature_at W β S
  apply Integrable.of_bound (ha.mul hm).aestronglyMeasurable |(T : ℝ) - S|
  apply ae_of_all
  intro w
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  exact (mul_le_mul (actualCurvatureProcess_abs_le W β S w)
    (curvature_time_integral_bound W β S T w) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem actual_curvature_cell_cross_moment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ w, actualParisiMagnetizationObservable W β H w *
      (actualCurvatureProcess W β S w * (W.B T w - W.B S w)) ∂W.law) =
      ∫ w, actualCurvatureProcess W β S w *
        (∫ r in (S : ℝ)..T, actualCurvatureProcess W β r w) ∂W.law := by
  have hh := LC1.actualFullProcess_brownian_past_cross_moment W β hβ S T H hST hTH
    (rawPastCurvature β S) (measurable_rawPastCurvature β S) 1 (rawPastCurvature_abs_le β S)
  have he := (rawPastCurvature_actual W β).mono (fun w hw => hw S)
  calc
    _ = ∫ w, rawPastCurvature β S (fun s : Iic S => W.B s.1 w) *
        actualParisiMagnetizationObservable W β H w * (W.B T w - W.B S w) ∂W.law := by
      apply integral_congr_ae
      filter_upwards [he] with w hw
      rw [hw]
      ring
    _ = _ := hh
    _ = ∫ r in (S : ℝ)..T, ∫ w, actualCurvatureProcess W β S w *
        actualCurvatureProcess W β r w ∂W.law := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (NNReal.coe_le_coe.mpr hST)] at hr
      have hr0 : 0 ≤ r := S.coe_nonneg.trans hr.1
      apply integral_congr_ae
      filter_upwards [he] with w hw
      rw [hw, Real.coe_toNNReal r hr0]
      unfold actualCurvatureProcess
      rfl
    _ = _ := (LC1.bounded_signed_interval_expectation_swap W.law S T
      (actualCurvatureProcess W β S)
      (measurable_curvature_at W β S)
      1 (actualCurvatureProcess_abs_le W β S) (actualCurvatureProcess W β)
      (measurable_actualCurvatureProcess W β) 1 (actualCurvatureProcess_abs_le W β)).symm

def actualCurvatureIntegratedSum (W : BrownianSystem Ω) (β : ℝ)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k * 2^l), actualCurvatureProcess W β (G.time l i) w *
    (∫ r in (G.time l i : ℝ)..(G.time l (i+1) : ℝ), actualCurvatureProcess W β r w)

lemma actualCurvatureIntegratedSum_bound (W : BrownianSystem Ω) (β : ℝ)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) (w : Ω) :
    |actualCurvatureIntegratedSum W β G k l w| ≤ (G.time 0 k : ℝ) := by
  unfold actualCurvatureIntegratedSum
  calc
    _ ≤ ∑ i ∈ Finset.range (k * 2^l), |actualCurvatureProcess W β (G.time l i) w *
        (∫ r in (G.time l i : ℝ)..(G.time l (i+1) : ℝ), actualCurvatureProcess W β r w)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k * 2^l), ((G.time l (i+1) : ℝ) - G.time l i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hh := (mul_le_mul (actualCurvatureProcess_abs_le W β (G.time l i) w)
        (curvature_time_integral_bound W β (G.time l i) (G.time l (i+1)) w)
        (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      have hdt : 0 ≤ (G.time l (i+1) : ℝ) - G.time l i :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr (G.monotone l (Nat.le_succ i)))
      rw [abs_of_nonneg hdt] at hh
      exact hh
    _ = _ := by
      rw [Finset.sum_range_sub (f := fun i => (G.time l i : ℝ))]
      simp only [G.duration, G.zero, NNReal.coe_zero, sub_zero]

theorem actual_curvature_leftSum_cross_moment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) :
    (∫ w, actualParisiMagnetizationObservable W β (G.time 0 k) w *
      actualCurvatureLeftSum W β G k l w ∂W.law) =
      ∫ w, actualCurvatureIntegratedSum W β G k l w ∂W.law := by
  let M := actualParisiMagnetizationObservable W β (G.time 0 k)
  have hi (i : ℕ) : Integrable (fun w => M w * (actualCurvatureProcess W β (G.time l i) w *
      (W.B (G.time l (i+1)) w - W.B (G.time l i) w))) W.law := by
    have hma := (measurable_actualParisiMagnetizationObservable W β (G.time 0 k)).mul
      (measurable_curvature_at W β (G.time l i))
    have hb (w : Ω) : |M w * actualCurvatureProcess W β (G.time l i) w| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (actualParisiMagnetizationObservable_abs_le W β (G.time 0 k) w)
        (actualCurvatureProcess_abs_le W β (G.time l i) w) (abs_nonneg _) zero_le_one).trans_eq (mul_one _)
    have hh := ((W.brownian.integrable_eval (G.time l (i+1))).sub (W.brownian.integrable_eval (G.time l i))).bdd_mul
      hma.aestronglyMeasurable (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hb w))
    convert hh using 1
    funext w
    dsimp only [Pi.mul_apply, Pi.sub_apply, M]
    ring
  unfold actualCurvatureLeftSum actualCurvatureIntegratedSum
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i),
    integral_finsetSum _ (fun i _ => curvature_integrated_term_integrable W β _ _)]
  apply Finset.sum_congr rfl
  intro i hi
  exact actual_curvature_cell_cross_moment W β hβ _ _ _ (G.monotone l (by omega))
    (G.le_duration (by have := Finset.mem_range.mp hi; omega))

theorem actual_curvature_leftSum_crossMoment_tendsto (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k * 2^l → (G.time l (i+1) : ℝ) - G.time l i ≤ δ l) :
    Tendsto (fun l => ∫ w, actualParisiMagnetizationObservable W β (G.time 0 k) w *
      actualCurvatureLeftSum W β G k l w ∂W.law) atTop
      (𝓝 (∫ r in (0 : ℝ)..(G.time 0 k : ℝ), actualParisiFullSusceptibilitySquareExpected W β r)) := by
  have hm (l : ℕ) : AEStronglyMeasurable (actualCurvatureIntegratedSum W β G k l) W.law := by
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_curvature_at W β (G.time l i)).mul
      (SKConstantsOAI.ZeroTemperatureSK.WeakIto.measurable_time_integral (Ω := Ω) (f := actualCurvatureProcess W β)
        (measurable_actualCurvatureProcess W β) _ _)
  have hpath : ∀ᵐ w ∂W.law, Tendsto (fun l => actualCurvatureIntegratedSum W β G k l w) atTop
      (𝓝 (∫ r in (0 : ℝ)..(G.time 0 k : ℝ), (actualCurvatureProcess W β r w)^2)) := by
    filter_upwards [actualCurvatureProcess_continuous_ae W β] with w hw
    exact integrated_product_quadrature_tendsto _ hw (actualCurvatureProcess_abs_le W β · w) G k δ hδ hwidth
  have h := tendsto_integral_of_dominated_convergence (μ := W.law) (bound := fun _ => (G.time 0 k : ℝ))
    hm (integrable_const _) (fun l => ae_of_all _ (fun w => by
      rw [Real.norm_eq_abs]; exact actualCurvatureIntegratedSum_bound W β G k l w)) hpath
  have hfub := LC1.bounded_interval_expectation_swap W.law 0 (G.time 0 k)
    (fun r w => (actualCurvatureProcess W β r w)^2)
    ((measurable_actualCurvatureProcess W β).pow_const 2) 1 (fun r w => by
      change |(actualCurvatureProcess W β r w)^2| ≤ (1 : ℝ)
      rw [abs_pow]
      nlinarith [actualCurvatureProcess_abs_le W β r w, abs_nonneg (actualCurvatureProcess W β r w)])
  rw [hfub] at h
  simpa only [actualParisiFullSusceptibilitySquareExpected, actualCurvatureProcess] using
    h.congr' (Filter.Eventually.of_forall (fun l => (actual_curvature_leftSum_cross_moment W β hβ G k l).symm))

end SKConstants.Completion.LBase
