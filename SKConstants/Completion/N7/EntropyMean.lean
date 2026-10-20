module

public import SKConstants.Completion.LM3.ScalarCancellation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport LC4a LM3
variable {Ω : Type*} [MeasurableSpace Ω]

theorem entropyReference_pre_at
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : V ≤ parisiEquilibriumPhysicalEndpoint β) :
    actualParisiEntropyReference W β V = Real.log 2 -
      ∫ w, binarySpinEntropy (actualParisiMagnetizationObservable W β V w) ∂W.law := by
  let ha : ∀ z, cdf (parisiEquilibriumMeasure β : Measure ℝ) z ∈ Icc (0 : ℝ) 1 :=
    fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have h1 : cdf (parisiEquilibriumMeasure β : Measure ℝ) 1 = 1 :=
    supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1
  have hVr : (V : ℝ) ∈ Icc 0 (β ^ 2 * parisiEquilibriumSupportEndpoint β) :=
    ⟨V.coe_nonneg, by
      rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
      exact NNReal.coe_le_coe.mpr hV⟩
  have HE := parisiEquilibrium_entropy_dissipation W β hβ ha h1 hVr
  have HL : (∫ w, binarySpinEntropy
      (scalarCDFGradient β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) ((V : ℝ) / β ^ 2)
        (Real.toNNReal (1 - (V : ℝ) / β ^ 2))
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) ha h1 V w))
      ∂W.law) = ∫ w, binarySpinEntropy (actualParisiMagnetizationObservable W β V w) ∂W.law := by
    simp only [actualParisiMagnetizationObservable, actualParisiFullMagnetization,
      cdfTimeClamp_eq (parisiPhysicalTime_mem_unit β hβ hVr), actualParisiFullScalarProcess,
      actualParisiFullScalarDrift, finiteTemperatureCDFProcess]
  simp only [Real.toNNReal_coe] at HE
  rw [HL] at HE
  have HI : (∫ v in (0 : ℝ)..(V : ℝ), actualParisiFullEntropyRateExpected W β v) =
      ∫ v in (0 : ℝ)..(V : ℝ), ∫ w,
        (scalarCDFHessian β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) (v / β ^ 2)
          (Real.toNNReal (1 - v / β ^ 2))
          (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) ha h1
            v.toNNReal w)) ^ 2 /
        (1 - (scalarCDFGradient β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) (v / β ^ 2)
          (Real.toNNReal (1 - v / β ^ 2))
          (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) ha h1
            v.toNNReal w)) ^ 2) ∂W.law := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le V.coe_nonneg] at hv
    exact actualParisiFullEntropyRateExpected_pre W β hβ ha h1 ⟨hv.1, hv.2.trans hVr.2⟩
  have HJ : actualParisiEntropyReference W β V =
      (1 / 2 : ℝ) * ∫ v in (0 : ℝ)..(V : ℝ), actualParisiFullEntropyRateExpected W β v := by
    unfold actualParisiEntropyReference
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le V.coe_nonneg] at hv
    dsimp only
    rw [actualParisiQueryRho_eq_one_pre W β hβ v
      (hv.2.trans (NNReal.coe_le_coe.mpr hV)), one_pow, one_mul]
  rw [HJ, HI]
  linarith

theorem sigmaSquare_cost_pre
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : V ≤ parisiEquilibriumPhysicalEndpoint β) :
    (∫ v in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β v) ^ 2 *
      actualParisiFullSusceptibilityExpected W β v) = 0 := by
  calc
    _ = ∫ _v in (0 : ℝ)..(V : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le V.coe_nonneg] at hv
      dsimp only
      rw [actualParisiQuerySigma_eq_zero_pre W β hβ v
        (hv.2.trans (NNReal.coe_le_coe.mpr hV))]
      simp
    _ = 0 := by simp

theorem scalar_information_balance_all_times
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∫ u, Real.log (actualParisiFullTerminalSpinDensity β W V u)
      ∂actualParisiFullTerminalSpinLaw β W V) -
      (1 / 2 : ℝ) * (∫ v in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β v) ^ 2 *
        actualParisiFullSusceptibilityExpected W β v) = actualParisiEntropyReference W β V := by
  rcases le_total V (parisiEquilibriumPhysicalEndpoint β) with hV | hV
  · rw [(actualTerminalLink_log_mean W β V).2, sigmaSquare_cost_pre W β hβ V hV,
      entropyReference_pre_at W β hβ V hV]
    ring
  · rw [← sigmaSquare_terminal_covariance W β hβ V]
    exact scalar_information_balance W β hβ V hV

end SKConstants.Completion.N7
