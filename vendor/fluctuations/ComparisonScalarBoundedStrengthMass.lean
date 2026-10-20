module

public import ComparisonOriginalMassCauchy
public import ComparisonStrengthRescaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 3500000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem comparison_scalar_weighted_error_factor (e F : ℝ) {x : ℝ} (hx : x ≠ 0) :
    |e*F/x^3|=|e/x^2| * |F/x| := by
  rw [←abs_mul]
  congr 1
  field_simp

theorem comparison_actual_bounded_strength_weighted_error_point
    {d lam x K : ℝ} (hd : 0 < d) (hlam : 0 ≤ lam) (hx : 0 < x)
    (hld : lam ≤ d^2) (hK : 0 ≤ K)
    (hwork : laplaceComparisonStrength d lam x/x^2 ≤ K) (r F : ℝ) :
    |laplaceComparisonStrength d lam r*F/x^3| ≤ (K+1)*|F/x| := by
  have he := comparison_strength_uniform_bound_of_working hd hlam hx hld hK hwork r
  rw [comparison_scalar_weighted_error_factor _ _ hx.ne',abs_of_nonneg he.1]
  exact mul_le_mul_of_nonneg_right he.2 (abs_nonneg _)

theorem comparison_actual_bounded_strength_weighted_integral_le
    (μ : Measure Ω) (R F : Ω → ℝ) (hR : Measurable R) (hi : Integrable F μ)
    {d lam x K : ℝ} (hd : 0 < d) (hlam : 0 ≤ lam) (hx : 0 < x)
    (hld : lam ≤ d^2) (hK : 0 ≤ K)
    (hwork : laplaceComparisonStrength d lam x/x^2 ≤ K) :
    Integrable (fun w => laplaceComparisonStrength d lam (R w)*F w/x^3) μ ∧
      (∫w, |laplaceComparisonStrength d lam (R w)*F w/x^3|∂μ) ≤
        (K+1)*(∫w, |F w/x|∂μ) := by
  have hbound w := comparison_actual_bounded_strength_weighted_error_point
    hd hlam hx hld hK hwork (R w) (F w)
  have he : Measurable (fun w => laplaceComparisonStrength d lam (R w)) :=
    (laplaceComparisonStrength_contDiff d lam).continuous.measurable.comp hR
  have hmeas : AEStronglyMeasurable
      (fun w => laplaceComparisonStrength d lam (R w)*F w/x^3) μ :=
    by simpa only [div_eq_mul_inv,Pi.mul_apply] using
      (he.aestronglyMeasurable.mul hi.aestronglyMeasurable).mul_const ((x^3)⁻¹)
  have hj : Integrable (fun w => (K+1)*|F w/x|) μ := (hi.div_const x).abs.const_mul _
  have hw : Integrable (fun w => laplaceComparisonStrength d lam (R w)*F w/x^3) μ :=
    hj.mono' hmeas (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hbound w)
  refine ⟨hw,?_⟩
  exact (integral_mono_ae hw.abs hj (Eventually.of_forall hbound)).trans_eq (integral_const_mul _ _)

theorem comparison_actual_bounded_strength_weighted_L1_tendsto
    (μ : ℕ → Measure Ω) (R F : ℕ → Ω → ℝ) (d lam x : ℕ → ℝ) {K : ℝ}
    (hR : ∀n, Measurable (R n)) (hi : ∀n, Integrable (F n) (μ n))
    (hd : ∀n, 0 < d n) (hlam : ∀n, 0 ≤ lam n) (hx : ∀n, 0 < x n)
    (hld : ∀n, lam n ≤ (d n)^2) (hK : 0 ≤ K)
    (hwork : ∀n, laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2 ≤ K)
    (hspin0 : Tendsto (fun n => ∫w, |F n w/x n|∂μ n) atTop (𝓝 0)) :
    (∀n, Integrable (fun w => laplaceComparisonStrength (d n) (lam n) (R n w)*F n w/(x n)^3) (μ n)) ∧
      Tendsto (fun n => ∫w, |laplaceComparisonStrength (d n) (lam n) (R n w)*F n w/(x n)^3|∂μ n)
        atTop (𝓝 0) := by
  have hh n := comparison_actual_bounded_strength_weighted_integral_le
    (μ n) (R n) (F n) (hR n) (hi n) (hd n) (hlam n) (hx n) (hld n) hK (hwork n)
  refine ⟨fun n => (hh n).1,?_⟩
  exact squeeze_zero (fun n => integral_nonneg (fun w => abs_nonneg _)) (fun n => (hh n).2)
    (by simpa using hspin0.const_mul (K+1))

theorem comparison_original_mass_bounded_strength_errors
    (μ : ℕ → Measure Ω) (hfinite : ∀n, IsFiniteMeasure (μ n))
    (R F : ℕ → Ω → ℝ) (d lam x : ℕ → ℝ) {C K : ℝ}
    (hR : ∀n, Measurable (R n)) (hi : ∀n, Integrable (F n) (μ n))
    (hi2 : ∀n, Integrable (fun w => (F n w)^2) (μ n))
    (hd : ∀n, 0 < d n) (hlam : ∀n, 0 ≤ lam n) (hx : ∀n, 0 < x n)
    (hld : ∀n, lam n ≤ (d n)^2) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hmass : ∀n, (μ n).real univ ≤ C*x n)
    (hwork : ∀n, laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2 ≤ K)
    (hzero : Tendsto (fun n => (∫w, (F n w)^2∂μ n)/(x n)^3) atTop (𝓝 0)) :
    let ν := fun n => ENNReal.ofReal (1/x n) • μ n
    (∀n, Integrable (fun w => F n w/x n) (ν n)) ∧
      Tendsto (fun n => ∫w, |F n w/x n|∂ν n) atTop (𝓝 0) ∧
      (∀n, Integrable (fun w => laplaceComparisonStrength (d n) (lam n) (R n w)*F n w/(x n)^3) (ν n)) ∧
      Tendsto (fun n => ∫w, |laplaceComparisonStrength (d n) (lam n) (R n w)*F n w/(x n)^3|∂ν n)
        atTop (𝓝 0) := by
  dsimp only
  have hni n : Integrable (F n) (ENNReal.ofReal (1/x n) • μ n) :=
    (hi n).smul_measure ENNReal.ofReal_ne_top
  have hspin := comparison_original_mass_normalized_L1_tendsto μ hfinite F x hx hC hi hi2 hmass hzero
  have hweighted := comparison_actual_bounded_strength_weighted_L1_tendsto
    (fun n => ENNReal.ofReal (1/x n) • μ n) R F d lam x hR hni hd hlam hx hld hK hwork hspin
  exact ⟨fun n => (hni n).div_const _,hspin,hweighted.1,hweighted.2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
