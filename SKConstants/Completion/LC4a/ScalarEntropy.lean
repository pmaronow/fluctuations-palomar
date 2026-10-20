module
public import SKConstants.Completion.LC4a.PositiveDensity
public import SKConstants.ParisiScalarEnergyPreReference
public import SKConstants.ParisiFullRowSecondMoment

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma spinLink_log_mean (β v y : ℝ) :
    (∫ b, actualParisiSpinLinkDensity β b v y * Real.log (actualParisiSpinLinkDensity β b v y)
      ∂scalarHiddenPriorBool 0) =
      Real.log 2 - binarySpinEntropy (actualParisiFullMagnetization β v y) := by
  rw [integral_scalarHiddenPriorBool_zero_fullPosterior,
    binarySpinEntropy_log_formula _ (by
      exact abs_lt.mpr (actualParisiFullMagnetization_strict_bounds β v y))]
  simp only [actualParisiSpinLinkDensity, scalarHiddenSign, Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_mul]
  ring

theorem actualTerminalLink_log_mean (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    Integrable (fun u => Real.log (actualParisiFullTerminalSpinDensity β W V u))
      (actualParisiFullTerminalSpinLaw β W V) ∧
      (∫ u, Real.log (actualParisiFullTerminalSpinDensity β W V u)
        ∂actualParisiFullTerminalSpinLaw β W V) =
        Real.log 2 - ∫ w, binarySpinEntropy (actualParisiMagnetizationObservable W β V w) ∂W.law := by
  let := W.isProbability
  let μ := (scalarHiddenPriorBool 0).prod W.law
  let L := actualParisiFullTerminalSpinDensity β W V
  have hm : Measurable L := measurable_actualParisiFullTerminalSpinDensity β W V
  have hp : ∀ u, 0 < L u := actualParisiFullTerminalSpinDensity_pos β W V
  have hb : ∀ u, L u ≤ 2 := fun u => actualParisiSpinLinkDensity_le_two β u.1 V _
  have hi := integrable_log_withDensity_of_bounded μ L hm (fun u => (hp u).le) 2 hb
  refine ⟨hi, ?_⟩
  have hLi : Integrable (fun u => L u * Real.log (L u)) μ :=
    Integrable.of_bound (hm.mul hm.log).aestronglyMeasurable 5 (ae_of_all _ (fun u => by
      simpa only [Real.norm_eq_abs, show (2 : ℝ)^2 + 1 = 5 by norm_num] using
        abs_mul_log_le (L u) 2 (hp u).le (hb u)))
  have hw := integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)) (fun u => Real.log (L u))
  change (∫ u, Real.log (L u) ∂actualParisiFullTerminalSpinLaw β W V) = _ at hw
  simp only [ENNReal.toReal_ofReal (hp _).le, smul_eq_mul] at hw
  rw [hw, integral_prod_symm _ hLi]
  have he (w : Ω) : (∫ b, L (b, w) * Real.log (L (b, w)) ∂scalarHiddenPriorBool 0) =
      Real.log 2 - binarySpinEntropy (actualParisiMagnetizationObservable W β V w) :=
    spinLink_log_mean β V (actualParisiFullTerminalField β W V w)
  simp_rw [he]
  have hc : Continuous binarySpinEntropy := by
    unfold binarySpinEntropy
    fun_prop
  have hH : Integrable (fun w => binarySpinEntropy (actualParisiMagnetizationObservable W β V w))
      W.law := by
    apply Integrable.of_bound
      (hc.measurable.comp (measurable_actualParisiMagnetizationObservable W β V)).aestronglyMeasurable
      (Real.log 2)
    exact ae_of_all _ (fun w => by
      change ‖binarySpinEntropy (actualParisiFullMagnetization β V
        (actualParisiFullScalarProcess W β V w))‖ ≤ Real.log 2
      rw [Real.norm_eq_abs, abs_of_nonneg (binarySpinEntropy_bounds
        (actualParisiFullMagnetization_curvature_bounds β V _).1).1]
      exact (binarySpinEntropy_bounds (actualParisiFullMagnetization_curvature_bounds β V _).1).2)
  rw [integral_sub (integrable_const _) hH, integral_const]
  simp

lemma entropyRate_eq_defect_after_support (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ v) :
    actualParisiFullEntropyRateExpected W β v = actualParisiFullDefectMoment W β v := by
  have hv' : β^2 * parisiEquilibriumSupportEndpoint β ≤ v := by
    rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
    exact hv
  unfold actualParisiFullEntropyRateExpected actualParisiFullDefectMoment
  apply integral_congr_ae
  apply ae_of_all
  intro w
  dsimp only
  rw [actualParisiFullCurvature_eq_tanh_after_support β hβ v _ hv',
    actualParisiFullMagnetization_eq_tanh_after_support β hβ v hv']
  change (scalarDefect _)^2 / scalarDefect _ = scalarDefect _
  field_simp

theorem actualTerminalEntropy_reference_balance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    Real.log 2 - (∫ w, binarySpinEntropy (actualParisiMagnetizationObservable W β V w) ∂W.law) =
      actualParisiEntropyReference W β V +
        (1 / 2 : ℝ) * (∫ v in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
          (actualParisiQuerySigma W β v)^2 * actualParisiFullSusceptibilityExpected W β v) := by
  let a := parisiEquilibriumPhysicalEndpoint β
  have haV : (a : ℝ) ≤ V := hV
  have hpre := actualParisiEntropyReference_pre W β hβ
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1)
  have hpost := actualParisi_post_entropy_dissipation W β hβ V haV
  have ht : (∫ w, binarySpinEntropy (actualParisiMagnetizationObservable W β V w) ∂W.law) =
      ∫ w, binarySpinEntropy (Real.tanh (actualParisiFullScalarProcess W β V w)) ∂W.law := by
    apply integral_congr_ae
    apply ae_of_all
    intro w
    change binarySpinEntropy (actualParisiFullMagnetization β V
      (actualParisiFullScalarProcess W β V w)) = _
    rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ V (by
        rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
        exact haV)]
  have href : actualParisiEntropyReference W β V = actualParisiEntropyReference W β a +
      (1 / 2 : ℝ) * (∫ v in (a : ℝ)..(V : ℝ), (actualParisiQueryRho W β v)^2 *
        actualParisiFullEntropyRateExpected W β v) := by
    unfold actualParisiEntropyReference
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (actualParisiEntropyIntegrand_intervalIntegrable W β 0 a)
      (actualParisiEntropyIntegrand_intervalIntegrable W β a V)]
    ring
  have hsum : (∫ v in (a : ℝ)..(V : ℝ), (actualParisiQueryRho W β v)^2 *
      actualParisiFullEntropyRateExpected W β v) +
      (∫ v in (a : ℝ)..(V : ℝ), (actualParisiQuerySigma W β v)^2 *
        actualParisiFullSusceptibilityExpected W β v) =
      ∫ v in (a : ℝ)..(V : ℝ), actualParisiFullDefectMoment W β v := by
    rw [← intervalIntegral.integral_add
      (f := fun v => (actualParisiQueryRho W β v)^2 * actualParisiFullEntropyRateExpected W β v)
      (g := fun v => (actualParisiQuerySigma W β v)^2 * actualParisiFullSusceptibilityExpected W β v)
      (actualParisiEntropyIntegrand_intervalIntegrable W β a V)
      ((((continuous_actualParisiQuerySigma W β).pow 2).mul
        (continuous_actualParisiFullSusceptibilityExpected W β)).intervalIntegrable a V)]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le haV] at hv
    dsimp only
    have hp : actualParisiFullEntropyRateExpected W β v =
        actualParisiFullSusceptibilityExpected W β v := by
      have H := actualParisiFullEntropyRateExpected_post W β hβ (v - a) (by linarith [hv.1])
      have P := actualParisiFullSusceptibilityExpected_post W β hβ (v - a) (by linarith [hv.1])
      rw [add_sub_cancel] at H P
      exact H.trans P.symm
    rw [← hp, ← add_mul, actualParisiQueryRhoSigma_unit W β hβ v, one_mul]
    exact entropyRate_eq_defect_after_support W β hβ v hv.1
  rw [ht, href, hpre]
  simp only [Real.toNNReal_coe] at hpost
  change _ = actualParisiEndpointEntropy W β - _ at hpost
  linarith [hpost, hsum]

end SKConstants.Completion.LC4a
