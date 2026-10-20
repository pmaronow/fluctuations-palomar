module

public import SKConstants.ParisiFullMixedRows
public import SKConstants.ParisiScalarEnergyMomentIdentification
public import SKConstants.ParisiFullVarianceIntegral
public import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem sign_fourth_average (m : ℝ) :
    (1 / 2 : ℝ) * (1 + m) * (1 - m) ^ 4 +
      (1 / 2 : ℝ) * (1 - m) * (-1 - m) ^ 4 =
      4 * (1 - m ^ 2) - 3 * (1 - m ^ 2) ^ 2 := by ring

theorem actual_terminal_curvature (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) (w : Ω) :
    actualParisiFullCurvature β V (actualParisiFullScalarProcess W β V w) =
      1 - (actualParisiFullPosteriorMean W β V w) ^ 2 := by
  have ht : β ^ 2 * parisiEquilibriumSupportEndpoint β ≤ (V : ℝ) := by
    rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
    exact_mod_cast hV
  rw [actualParisiFullCurvature_eq_tanh_after_support β hβ _ _ ht]
  change 1 - (Real.tanh _) ^ 2 = 1 - (actualParisiFullMagnetization β V _) ^ 2
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ _ ht]

theorem actual_terminal_error_mean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    (∫ u, actualParisiPinningError W β V u ∂actualParisiFullTerminalSpinLaw β W V) =
      actualParisiFullSusceptibilityExpected W β V := by
  let := W.isProbability
  rw [actualParisiPinningError_mean W β hβ V V le_rfl]
  unfold actualParisiFullSusceptibilityExpected
  simp only [Real.toNNReal_coe]
  simp_rw [actual_terminal_curvature W β hβ V hV]
  rw [integral_sub (integrable_const 1)]
  · simp
  · exact Integrable.of_bound
      ((measurable_actualParisiFullPosteriorMean W β V).pow_const 2).aestronglyMeasurable 1
      (ae_of_all _ (fun w => by
        rw [Real.norm_eq_abs, abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg _)
          (abs_actualParisiFullPosteriorMean_le W β V w) 2))

theorem actual_terminal_error_secondMoment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    (∫ u, (actualParisiPinningError W β V u) ^ 2 ∂actualParisiFullTerminalSpinLaw β W V) =
      4 * actualParisiFullSusceptibilityExpected W β V -
        3 * actualParisiFullSusceptibilitySquareExpected W β V := by
  let := W.isProbability
  have hb (u : Bool × Ω) : |actualParisiPinningError W β V u ^ 2| ≤ 16 := by
    rw [abs_pow, abs_of_nonneg (actualParisiPinningError_mem_Icc W β V u).1]
    nlinarith [(actualParisiPinningError_mem_Icc W β V u).2,
      (actualParisiPinningError_mem_Icc W β V u).1]
  rw [actualParisiFullTerminalSpinLaw_integral_bounded W β V _
    ((measurable_actualParisiPinningError W β V).pow_const 2) 16 hb]
  have he (w : Ω) :
      (1 / 2 : ℝ) * (1 + actualParisiFullPosteriorMean W β V w) *
          actualParisiPinningError W β V (true, w) ^ 2 +
        (1 / 2 : ℝ) * (1 - actualParisiFullPosteriorMean W β V w) *
          actualParisiPinningError W β V (false, w) ^ 2 =
        4 * (1 - (actualParisiFullPosteriorMean W β V w) ^ 2) -
          3 * (1 - (actualParisiFullPosteriorMean W β V w) ^ 2) ^ 2 := by
    simp only [actualParisiPinningError, scalarHiddenSign, Bool.false_eq_true, ↓reduceIte]
    ring
  simp_rw [he, ← actual_terminal_curvature W β hβ V hV]
  have hm : Measurable (fun w =>
      actualParisiFullCurvature β V (actualParisiFullScalarProcess W β V w)) := by
    exact ((continuous_actualParisiFullCurvature β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
      (measurable_actualParisiPreContinuationField W β V)
  have hi : Integrable (fun w =>
      actualParisiFullCurvature β V (actualParisiFullScalarProcess W β V w)) W.law :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using
        actualParisiFullCurvature_abs_le_one β V (actualParisiFullScalarProcess W β V w)))
  have hi2 : Integrable (fun w =>
      actualParisiFullCurvature β V (actualParisiFullScalarProcess W β V w) ^ 2) W.law :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1
      (ae_of_all _ (fun w => by
        rw [Real.norm_eq_abs, abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg _)
          (actualParisiFullCurvature_abs_le_one β V (actualParisiFullScalarProcess W β V w)) 2))
  rw [integral_sub (hi.const_mul 4) (hi2.const_mul 3), integral_const_mul, integral_const_mul]
  simp only [actualParisiFullSusceptibilityExpected,
    actualParisiFullSusceptibilitySquareExpected, Real.toNNReal_coe]

def terminalFluctuation (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (u : Bool × Ω) : ℝ :=
  (β ^ 2 * actualParisiFullSusceptibilityExpected W β V / 2) *
    (actualParisiPinningError W β V u - actualParisiFullSusceptibilityExpected W β V)

theorem measurable_terminalFluctuation (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    Measurable (terminalFluctuation W β V) :=
  ((measurable_actualParisiPinningError W β V).sub_const _).const_mul _

theorem terminalFluctuation_mean_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    (∫ u, terminalFluctuation W β V u ∂actualParisiFullTerminalSpinLaw β W V) = 0 := by
  have hi : Integrable (actualParisiPinningError W β V) (actualParisiFullTerminalSpinLaw β W V) :=
    Integrable.of_bound (measurable_actualParisiPinningError W β V).aestronglyMeasurable 4
      (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (actualParisiPinningError_mem_Icc W β V u).1]
        exact (actualParisiPinningError_mem_Icc W β V u).2))
  unfold terminalFluctuation
  rw [integral_const_mul, integral_sub hi (integrable_const _),
    actual_terminal_error_mean W β hβ V hV]
  simp

theorem terminalFluctuation_variance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    Var[terminalFluctuation W β V; actualParisiFullTerminalSpinLaw β W V] =
      β ^ 4 * (actualParisiFullSusceptibilityExpected W β V) ^ 2 / 4 *
        (4 * actualParisiFullSusceptibilityExpected W β V -
          3 * actualParisiFullSusceptibilitySquareExpected W β V -
          (actualParisiFullSusceptibilityExpected W β V) ^ 2) := by
  have hi : MemLp (actualParisiPinningError W β V) 2 (actualParisiFullTerminalSpinLaw β W V) :=
    memLp_of_bounded (ae_of_all _ (actualParisiPinningError_mem_Icc W β V))
      (measurable_actualParisiPinningError W β V).aestronglyMeasurable 2
  unfold terminalFluctuation
  rw [variance_const_mul, variance_sub_const hi.aestronglyMeasurable,
    variance_eq_sub hi, actual_terminal_error_mean W β hβ V hV]
  change _ * ((∫ u, actualParisiPinningError W β V u ^ 2
    ∂actualParisiFullTerminalSpinLaw β W V) - _) = _
  rw [actual_terminal_error_secondMoment W β hβ V hV]
  ring

theorem terminalFluctuation_variance_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    Var[terminalFluctuation W β V; actualParisiFullTerminalSpinLaw β W V] ≤
      β ^ 4 * (actualParisiFullSusceptibilityExpected W β V) ^ 3 := by
  rw [terminalFluctuation_variance W β hβ V hV]
  have hr : 0 ≤ actualParisiFullSusceptibilitySquareExpected W β V :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hh : 4 * actualParisiFullSusceptibilityExpected W β V -
      3 * actualParisiFullSusceptibilitySquareExpected W β V -
      (actualParisiFullSusceptibilityExpected W β V) ^ 2 ≤
      4 * actualParisiFullSusceptibilityExpected W β V := by
    nlinarith [sq_nonneg (actualParisiFullSusceptibilityExpected W β V)]
  calc
    _ ≤ (β ^ 4 * (actualParisiFullSusceptibilityExpected W β V) ^ 2 / 4) *
        (4 * actualParisiFullSusceptibilityExpected W β V) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem terminalFluctuation_abs_le (W : BrownianSystem Ω) (β : ℝ)
    (V : ℝ≥0) (u : Bool × Ω) :
    |terminalFluctuation W β V u| ≤
      2 * β ^ 2 * actualParisiFullSusceptibilityExpected W β V := by
  let := W.isProbability
  have hp0 : 0 ≤ actualParisiFullSusceptibilityExpected W β V :=
    integral_nonneg (fun w => (actualParisiFullMagnetization_curvature_bounds β V _).2.1)
  have hp1 : actualParisiFullSusceptibilityExpected W β V ≤ 1 := by
    calc
      _ ≤ ∫ _ : Ω, (1 : ℝ) ∂W.law := by
        apply integral_mono_of_nonneg
          (ae_of_all _ (fun w => (actualParisiFullMagnetization_curvature_bounds β V _).2.1))
          (integrable_const 1)
        exact ae_of_all _ (fun w => (le_abs_self _).trans
          (actualParisiFullCurvature_abs_le_one β V _))
      _ = 1 := by simp
  obtain ⟨he0, he4⟩ := actualParisiPinningError_mem_Icc W β V u
  have hd : |actualParisiPinningError W β V u - actualParisiFullSusceptibilityExpected W β V| ≤ 4 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  unfold terminalFluctuation
  rw [abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg β) hp0 |> fun h => div_nonneg h (by norm_num))]
  calc
    _ ≤ (β ^ 2 * actualParisiFullSusceptibilityExpected W β V / 2) * 4 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

theorem query_terminalFluctuation_variance_le (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    Var[fun u => terminalFluctuation W β V u.1; actualParisiFullQuerySpinLaw W Z β V] ≤
      β ^ 4 * (actualParisiFullSusceptibilityExpected W β V) ^ 3 := by
  have hv := variance_map (measurable_terminalFluctuation W β V).aemeasurable
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).aemeasurable
  rw [(actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).map_eq] at hv
  exact hv ▸ terminalFluctuation_variance_le W β hβ V hV

end SKConstants.Completion.LJ
