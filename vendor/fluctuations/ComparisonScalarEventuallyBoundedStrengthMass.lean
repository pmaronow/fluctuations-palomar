module

public import ComparisonScalarBoundedStrengthMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 3500000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem comparison_actual_eventually_bounded_strength_weighted_L1_tendsto
    (μ : ℕ → Measure Ω) (R F : ℕ → Ω → ℝ) (d lam x : ℕ → ℝ) {K : ℝ}
    (hR : ∀n, Measurable (R n)) (hi : ∀n, Integrable (F n) (μ n))
    (hd : ∀n, 0 < d n) (hlam : ∀n, 0 ≤ lam n) (hx : ∀n, 0 < x n)
    (hld : ∀n, lam n ≤ (d n)^2) (hK : 0 ≤ K)
    (hwork : ∀ᶠn in atTop, laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2 ≤ K)
    (hspin0 : Tendsto (fun n => ∫w, |F n w/x n|∂μ n) atTop (𝓝 0)) :
    (∀n, Integrable (fun w => laplaceComparisonStrength (d n) (lam n) (R n w)*F n w/(x n)^3) (μ n)) ∧
      Tendsto (fun n => ∫w, |laplaceComparisonStrength (d n) (lam n) (R n w)*F n w/(x n)^3|∂μ n)
        atTop (𝓝 0) := by
  have hii n := comparison_actual_bounded_strength_weighted_integral_le
    (μ n) (R n) (F n) (hR n) (hi n) (hd n) (hlam n) (hx n) (hld n)
    (K:=laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)
    (by
      unfold laplaceComparisonStrength comparisonStrength
      exact div_nonneg (mul_nonneg (hlam n) (laplaceComparisonShape_pos _).le) (sq_nonneg _)) le_rfl
  refine ⟨fun n=>(hii n).1,?_⟩
  apply squeeze_zero' (Eventually.of_forall fun _=>integral_nonneg (fun _=>abs_nonneg _)) _
    (by simpa using hspin0.const_mul (K+1))
  filter_upwards [hwork] with n hn
  exact (comparison_actual_bounded_strength_weighted_integral_le
    (μ n) (R n) (F n) (hR n) (hi n) (hd n) (hlam n) (hx n) (hld n) hK hn).2

theorem comparison_original_mass_eventually_bounded_strength_errors
    (μ : ℕ → Measure Ω) (hfinite : ∀n, IsFiniteMeasure (μ n))
    (R F : ℕ → Ω → ℝ) (d lam x : ℕ → ℝ) {C K : ℝ}
    (hR : ∀n, Measurable (R n)) (hi : ∀n, Integrable (F n) (μ n))
    (hi2 : ∀n, Integrable (fun w => (F n w)^2) (μ n))
    (hd : ∀n, 0 < d n) (hlam : ∀n, 0 ≤ lam n) (hx : ∀n, 0 < x n)
    (hld : ∀n, lam n ≤ (d n)^2) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hmass : ∀n, (μ n).real univ ≤ C*x n)
    (hwork : ∀ᶠn in atTop, laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2 ≤ K)
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
  have hweighted := comparison_actual_eventually_bounded_strength_weighted_L1_tendsto
    (fun n => ENNReal.ofReal (1/x n) • μ n) R F d lam x hR hni hd hlam hx hld hK hwork hspin
  exact ⟨fun n => (hni n).div_const _,hspin,hweighted.1,hweighted.2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
