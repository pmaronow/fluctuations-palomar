module

public import SKConstants.ParisiScalarEnergyProfiles

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

lemma parisiPhysicalTime_mem_unit (β : ℝ) (hβ : 1<β) {v : ℝ}
    (hv : v∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) : v/β^2∈Icc (0:ℝ) 1 := by
  have hb := sq_pos_of_pos (zero_lt_one.trans hβ)
  refine ⟨div_nonneg hv.1 hb.le,?_⟩
  apply (div_le_iff₀ hb).mpr
  rw [one_mul]
  exact hv.2.trans (mul_le_of_le_one_right hb.le
    (parisiEquilibriumSupportEndpoint_spec β hβ).1.2.le)

theorem actualParisiFullSusceptibilityExpected_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z,cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1) {v : ℝ}
    (hv : v∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) :
    actualParisiFullSusceptibilityExpected W β v=parisiPreSusceptibilityExpected W β ha h1 v := by
  simp only [actualParisiFullSusceptibilityExpected,actualParisiFullCurvature,
    cdfTimeClamp_eq (parisiPhysicalTime_mem_unit β hβ hv),parisiPreSusceptibilityExpected,
    actualParisiFullScalarProcess,actualParisiFullScalarDrift,finiteTemperatureCDFProcess]

theorem actualParisiFullEntropyRateExpected_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z,cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1) {v : ℝ}
    (hv : v∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) :
    actualParisiFullEntropyRateExpected W β v=
      ∫ w, (scalarCDFHessian β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (v/β^2)
        (Real.toNNReal (1-v/β^2))
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
          (Real.toNNReal v) w))^2/
        (1-(scalarCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (v/β^2)
          (Real.toNNReal (1-v/β^2))
          (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
            (Real.toNNReal v) w))^2) ∂W.law := by
  simp only [actualParisiFullEntropyRateExpected,actualParisiFullCurvature,
    actualParisiFullMagnetization,cdfTimeClamp_eq (parisiPhysicalTime_mem_unit β hβ hv),
    actualParisiFullScalarProcess,actualParisiFullScalarDrift,finiteTemperatureCDFProcess]

theorem actualParisiFullSusceptibilityExpected_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (v : ℝ) (hv : 0≤v) :
    actualParisiFullSusceptibilityExpected W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v)=
      actualParisiContinuationP W β v := by
  rw [actualParisiContinuationP_eq_full_process_moment W β hβ v hv]
  have ht : β^2*parisiEquilibriumSupportEndpoint β≤
      (parisiEquilibriumPhysicalEndpoint β:ℝ)+v := by
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
    linarith
  unfold actualParisiFullSusceptibilityExpected
  apply integral_congr_ae
  filter_upwards [] with w
  rw [actualParisiFullCurvature_eq_tanh_after_support β hβ _ _ ht]
  change scalarDefect (actualParisiFullScalarProcess W β
    (Real.toNNReal ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v)) w)=_
  rw [Real.toNNReal_add (parisiEquilibriumPhysicalEndpoint β).coe_nonneg hv,Real.toNNReal_coe]

theorem actualParisiFullEntropyRateExpected_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (v : ℝ) (hv : 0≤v) :
    actualParisiFullEntropyRateExpected W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+v)=
      actualParisiContinuationP W β v := by
  rw [←actualParisiFullSusceptibilityExpected_post W β hβ v hv]
  have ht : β^2*parisiEquilibriumSupportEndpoint β≤
      (parisiEquilibriumPhysicalEndpoint β:ℝ)+v := by
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
    linarith
  unfold actualParisiFullEntropyRateExpected actualParisiFullSusceptibilityExpected
  apply integral_congr_ae
  filter_upwards [] with w
  rw [actualParisiFullCurvature_eq_tanh_after_support β hβ _ _ ht,
    actualParisiFullMagnetization_eq_tanh_after_support β hβ _ ht]
  change (scalarDefect _)^2/scalarDefect _=scalarDefect _
  field_simp

theorem actualParisiContinuationP_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) :
    actualParisiContinuationP W β 0=1-parisiEquilibriumSupportEndpoint β := by
  have Hpre := actualParisiFullOverlap_pre W β hβ (parisiEquilibriumPhysicalEndpoint β) le_rfl
  have Hpost := actualParisiFullOverlap_post W β hβ 0
  rw [add_zero,NNReal.coe_zero] at Hpost
  rw [parisiEquilibriumPhysicalEndpoint_coe β hβ] at Hpre
  have hbn : β^2≠0 := pow_ne_zero 2 (zero_lt_one.trans hβ).ne'
  rw [mul_div_cancel_left₀ _ hbn] at Hpre
  linarith

end SKConstants
