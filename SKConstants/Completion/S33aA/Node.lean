module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.Completion.S33aA.LogCosh
public import SKConstants.Completion.S33aA.ActualRotation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S33aA
open SKConstantsOAI.ZeroTemperatureSK Blueprint4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization

omit [MeasurableSpace A] in
theorem terminalLogLink_eq_after_support (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) (t : ℝ≥0) (ht : parisiEquilibriumPhysicalEndpoint β ≤ t)
    (u : Bool × Ω) :
    Real.log (actualParisiFullTerminalSpinDensity β W t u) =
      scalarHiddenSign u.1 * actualParisiFullScalarProcess W β t u.2 -
        scalarLogCosh (actualParisiFullScalarProcess W β t u.2) := by
  change Real.log (1 + scalarHiddenSign u.1 *
    actualParisiFullMagnetization β t (actualParisiFullScalarProcess W β t u.2)) = _
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ t (by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ht)]
  exact LJ.log_sign_tanh_link u.1 _

omit [MeasurableSpace A] in
theorem rowDCoefficient_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (u : (Bool × Ω) × A) :
    LM4b.actualRowDCoefficient W β t u = actualParisiQuerySigma W β t *
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2) :=
  LM4b.actualRowDCoefficient_eq_defect W β hβ t u

omit [MeasurableSpace A] in
theorem rowBracketIntegrand_cancel (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (u : (Bool × Ω) × A) :
    actualParisiPinningError W β t u.1 -
        (LM4b.actualRowDCoefficient W β t u) ^ 2 =
      β ^ 2 * actualParisiFullSusceptibilitySquareExpected W β t *
        actualParisiPinningError W β t u.1 := by
  rw [rowDCoefficient_eq W β hβ]
  have hunit := actualParisiQueryRhoSigma_unit W β hβ t
  rw [LQ.actual_rho_sq_eq W β hβ t t.coe_nonneg] at hunit
  have hs : 1 - (actualParisiQuerySigma W β t) ^ 2 =
      β ^ 2 * actualParisiFullSusceptibilitySquareExpected W β t := by linarith
  change (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2) ^ 2 -
    (actualParisiQuerySigma W β t *
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2)) ^ 2 = _
  dsimp only [actualParisiPinningError]
  calc
    _ = (1 - (actualParisiQuerySigma W β t) ^ 2) *
        (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β t u.1.2) ^ 2 := by ring
    _ = _ := by rw [hs]

omit [MeasurableSpace A] in
theorem posterior_real_continuous (W : BrownianSystem Ω) (β : ℝ) (w : Ω)
    (hY : Continuous (fun t => actualParisiFullScalarProcess W β t w)) :
    Continuous (fun t : ℝ => actualParisiFullPosteriorMean W β t.toNNReal w) := by
  change Continuous (fun t : ℝ => actualParisiFullMagnetization β (t.toNNReal : ℝ)
    (actualParisiFullScalarProcess W β t.toNNReal w))
  exact (continuous_actualParisiFullMagnetization β).comp
    (((NNReal.continuous_coe).comp continuous_real_toNNReal).prodMk
      (hY.comp continuous_real_toNNReal))

omit [MeasurableSpace A] in
theorem rowDCoefficient_continuous (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (u : (Bool × Ω) × A)
    (hY : Continuous (fun t => actualParisiFullScalarProcess W β t u.1.2)) :
    Continuous (fun t : ℝ => LM4b.actualRowDCoefficient W β t.toNNReal u) := by
  simp_rw [rowDCoefficient_eq W β hβ]
  exact ((continuous_actualParisiQuerySigma W β).comp
    (NNReal.continuous_coe.comp continuous_real_toNNReal)).mul
      (continuous_const.sub (posterior_real_continuous W β u.1.2 hY))

omit [MeasurableSpace A] in
theorem rowDBracket_eq_post_of_continuous (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (u : (Bool × Ω) × A)
    (hY : Continuous (fun t => actualParisiFullScalarProcess W β t u.1.2)) :
    LM4b.actualRowDBracket W β V u =
      ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
        (actualParisiQuerySigma W β t.toNNReal) ^ 2 *
          actualParisiPinningError W β t.toNNReal u.1 := by
  let S := parisiEquilibriumPhysicalEndpoint β
  have hc : Continuous (fun t : ℝ => (LM4b.actualRowDCoefficient W β t.toNNReal u) ^ 2) :=
    (rowDCoefficient_continuous W β hβ u hY).pow 2
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 S) (hc.intervalIntegrable (μ := volume) S V)
  change LM4b.actualRowDBracket W β S u +
    (∫ t in (S : ℝ)..(V : ℝ), (LM4b.actualRowDCoefficient W β t.toNNReal u) ^ 2) =
      LM4b.actualRowDBracket W β V u at he
  rw [SJ3.rowDBracket_eq_zero_pre W β hβ S le_rfl, zero_add] at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [rowDCoefficient_eq W β hβ, mul_pow]
  rfl

omit [MeasurableSpace A] in
theorem rowBracket_cancel_of_continuous (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) (u : (Bool × Ω) × A)
    (hY : Continuous (fun t => actualParisiFullScalarProcess W β t u.1.2)) :
    (∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
      actualParisiPinningError W β t.toNNReal u.1) - LM4b.actualRowDBracket W β V u =
      β ^ 2 * ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
        actualParisiFullSusceptibilitySquareExpected W β t *
          actualParisiPinningError W β t.toNNReal u.1 := by
  let S := parisiEquilibriumPhysicalEndpoint β
  have hm := posterior_real_continuous W β u.1.2 hY
  have hp : Continuous (fun t : ℝ => actualParisiPinningError W β t.toNNReal u.1) :=
    (continuous_const.sub hm).pow 2
  have hc : Continuous (fun t : ℝ => (LM4b.actualRowDCoefficient W β t.toNNReal u) ^ 2) :=
    (rowDCoefficient_continuous W β hβ u hY).pow 2
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 S) (hc.intervalIntegrable (μ := volume) S V)
  change LM4b.actualRowDBracket W β S u +
    (∫ t in (S : ℝ)..(V : ℝ), (LM4b.actualRowDCoefficient W β t.toNNReal u) ^ 2) =
      LM4b.actualRowDBracket W β V u at he
  rw [SJ3.rowDBracket_eq_zero_pre W β hβ S le_rfl, zero_add] at he
  change (∫ t in (S : ℝ)..(V : ℝ), actualParisiPinningError W β t.toNNReal u.1) -
    LM4b.actualRowDBracket W β V u = β ^ 2 * ∫ t in (S : ℝ)..(V : ℝ),
      actualParisiFullSusceptibilitySquareExpected W β t * actualParisiPinningError W β t.toNNReal u.1
  rw [← he, ← intervalIntegral.integral_sub (hp.intervalIntegrable (μ := volume) S V) (hc.intervalIntegrable (μ := volume) S V),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (NNReal.coe_le_coe.mpr hV)] at ht
  have ht0 : 0 ≤ t := S.coe_nonneg.trans ht.1
  have hh := rowBracketIntegrand_cancel W β hβ t.toNNReal u
  simpa only [Real.coe_toNNReal t ht0, mul_assoc] using hh

theorem rowBracket_cancel_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      (∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
        actualParisiPinningError W β t.toNNReal u.1) - LM4b.actualRowDBracket W β V u =
        β ^ 2 * ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
          actualParisiFullSusceptibilitySquareExpected W β t *
            actualParisiPinningError W β t.toNNReal u.1 := by
  let := W.isProbability
  let := Z.isProbability
  have hp : MeasurePreserving (fun u : (Bool × Ω) × A => u.1.2)
      (LM4.actualRowBaseLaw W Z) W.law :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
      (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law))
  filter_upwards [hp.quasiMeasurePreserving.ae
    ((actualParisiFullScalarDrift β).solution_continuous_ae W)] with u hu
  exact rowBracket_cancel_of_continuous W β hβ V hV u hu

theorem postSupportInformationIto_at_support (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (J Q Qs : (Bool × Ω) × A → ℝ)
    (hJ : LM4b.IsActualRowDIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) J)
    (hQ : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Q)
    (hQs : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Qs) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z,
      rowInformationV W β (parisiEquilibriumPhysicalEndpoint β) J u -
          Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u.1) -
          β * (Q u - Qs u) =
        -(β ^ 2 / 2) * ∫ t in (parisiEquilibriumPhysicalEndpoint β : ℝ)..
            (parisiEquilibriumPhysicalEndpoint β : ℝ),
          actualParisiFullSusceptibilitySquareExpected W β t *
            actualParisiPinningError W β t.toNNReal u.1 := by
  have hzero := SJ3.rowDIntegral_unique W Z β hβ (parisiEquilibriumPhysicalEndpoint β) hJ
    (SJ3.rowDIntegral_zero_pre W Z β hβ _ le_rfl)
  have hsame := SJ3.meanSquare_limit_unique (SJ3.measurable_queryRowLeftSum W Z β hβ _)
    hQ.2.1 hQs.2.1 hQ.2.2.1 hQ.2.2.2 hQs.2.2.2
  filter_upwards [hzero, hsame] with u hu hv
  simp only [rowInformationV, LM4.actualRowInformation, LM4.rowInformation, LM4.actualRowLink,
    SJ3.rowDBracket_eq_zero_pre W β hβ _ le_rfl, hu, hv,
    sub_self, mul_zero, sub_zero, zero_div, add_zero, intervalIntegral.integral_same]

omit [MeasurableSpace A] in
theorem postSignedEulerSum_log_error_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (m : ℕ) (b : Bool) (w : Ω) :
    postSignedEulerSum W β t m b w -
      (Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β + t m) (b, w)) -
        Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β + t 0) (b, w))) =
      postLogCoshError W β t m w := by
  rw [terminalLogLink_eq_after_support W β hβ _ (le_add_of_nonneg_right bot_le),
    terminalLogLink_eq_after_support W β hβ _ (le_add_of_nonneg_right bot_le)]
  exact postSignedEulerSum_error_eq W β t m b w

theorem postUniformSignedEulerSum_log_tendsto_L2 (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    (∀ n, Integrable (fun u : (Bool × Ω) × A =>
      (postSignedEulerSum W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u.1.1 u.1.2 -
        (Real.log (actualParisiFullTerminalSpinDensity β W
          (parisiEquilibriumPhysicalEndpoint β + scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u.1) -
          Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u.1))) ^ 2)
        (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun n => ∫ u : (Bool × Ω) × A,
      (postSignedEulerSum W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u.1.1 u.1.2 -
        (Real.log (actualParisiFullTerminalSpinDensity β W
          (parisiEquilibriumPhysicalEndpoint β + scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u.1) -
          Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u.1))) ^ 2
          ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  let := W.isProbability
  let := Z.isProbability
  have he (n : ℕ) (u : (Bool × Ω) × A) :
      postSignedEulerSum W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u.1.1 u.1.2 -
        (Real.log (actualParisiFullTerminalSpinDensity β W
          (parisiEquilibriumPhysicalEndpoint β + scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u.1) -
          Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u.1)) =
      postLogCoshError W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u.1.2 := by
    simpa only [scalarUniformTime_zero, add_zero] using
      postSignedEulerSum_log_error_eq W β hβ (scalarUniformTime n) _ u.1.1 u.1.2
  simp_rw [he]
  obtain ⟨hi, hlim⟩ := postUniformLogCoshError_tendsto_L2 W β hβ T
  refine ⟨fun n => ((hi n).comp_snd (scalarHiddenPriorBool 0)).comp_fst Z.law, ?_⟩
  have hp : MeasurePreserving (fun u : (Bool × Ω) × A => u.1.2)
      (LM4.actualRowBaseLaw W Z) W.law :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
      (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law))
  have hIntegral (n : ℕ) : (∫ u : (Bool × Ω) × A,
      (postLogCoshError W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u.1.2) ^ 2
        ∂LM4.actualRowBaseLaw W Z) =
      ∫ w, (postLogCoshError W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ w) ^ 2 ∂W.law :=
    hp.hasLaw.integral_comp (hi n).aestronglyMeasurable
  simp_rw [hIntegral]
  exact hlim

end SKConstants.Completion.S33aA
