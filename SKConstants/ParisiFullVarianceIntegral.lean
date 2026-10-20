module
public import SKConstants.ParisiScalarEnergyProfiles
public import SKConstants.ParisiFullRowMGFBudget

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullVarianceIntegral_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem actualParisiFullSusceptibilitySquareExpected_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) :
    actualParisiFullSusceptibilitySquareExpected W β t=1/β^2 := by
  have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have hq : (t:ℝ)/β^2 ∈ Icc (0:ℝ) 1 := by
    refine ⟨div_nonneg t.coe_nonneg hb.le,?_⟩
    apply (div_le_iff₀ hb).mpr
    have H := NNReal.coe_le_coe.mpr ht
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ] at H
    nlinarith [(parisiEquilibriumSupportEndpoint_spec β hβ).1.2]
  let ha : ∀ z,cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1 :=
    fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1 :=
    supported_probability_cdf_one (parisiEquilibriumMeasure β) (parisiEquilibriumMeasure_upstream_spec β).1
  have hv : (t:ℝ)∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β) := by
    refine ⟨t.coe_nonneg,?_⟩
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ht
  have H := (parisiEquilibrium_physicalBrownian_moments W β hβ ha h1 hv).2
  simpa only [actualParisiFullSusceptibilitySquareExpected,actualParisiFullCurvature,
    cdfTimeClamp_eq hq,actualParisiFullScalarProcess,actualParisiFullScalarDrift,
    finiteTemperatureCDFProcess,Real.toNNReal_coe] using H

theorem actualParisiFullSusceptibilitySquareExpected_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ≥0) (ht : parisiEquilibriumPhysicalEndpoint β ≤ t) :
    actualParisiFullSusceptibilitySquareExpected W β t=
      actualParisiContinuationR W β ((t-parisiEquilibriumPhysicalEndpoint β:ℝ≥0):ℝ) := by
  have htr : β^2*parisiEquilibriumSupportEndpoint β ≤ (t:ℝ) := by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ht
  rw [actualParisiContinuationR_eq_full_process_moment W β hβ _ (NNReal.coe_nonneg _)]
  simp only [Real.toNNReal_coe,actualParisiFullSusceptibilitySquareExpected,
    actualParisiFullCurvature_eq_tanh_after_support β hβ _ _ htr,scalarDefect,add_tsub_cancel_of_le ht]

theorem actualParisiContinuationP_variance_balance
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    (∫ v in S..T,actualParisiContinuationR W β v)=
      actualParisiContinuationP W β S-actualParisiContinuationP W β T := by
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hST
    (continuous_actualParisiContinuationP W β).continuousOn
    (fun x hx => actualParisiContinuationP_hasDerivWithinAt_right W β hβ x (hS.trans hx.1.le))
    ((continuous_actualParisiContinuationR W β).neg.intervalIntegrable S T)
  simp only [Pi.neg_apply,intervalIntegral.integral_neg] at H
  linarith

lemma actualParisiFullSusceptibilitySquareExpected_interval_pre
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) (hST : S ≤ T)
    (hTV : T ≤ parisiEquilibriumPhysicalEndpoint β) :
    (∫ v in (S:ℝ)..T,actualParisiFullSusceptibilitySquareExpected W β v)=
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  have he : (∫ v in (S:ℝ)..T,actualParisiFullSusceptibilitySquareExpected W β v)=
      ∫ v in (S:ℝ)..T,(1/β^2:ℝ) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (NNReal.coe_le_coe.mpr hST)] at hv
    have hv0 := S.coe_nonneg.trans hv.1
    simpa only [Real.coe_toNNReal v hv0] using
      actualParisiFullSusceptibilitySquareExpected_pre W β hβ v.toNNReal
        (by apply NNReal.coe_le_coe.mp; rw [Real.coe_toNNReal v hv0]; exact hv.2.trans (NNReal.coe_le_coe.mpr hTV))
  rw [he,intervalIntegral.integral_const,actualParisiFullOverlap_pre W β hβ T hTV,
    actualParisiFullOverlap_pre W β hβ S (hST.trans hTV)]
  simp only [smul_eq_mul]
  ring

lemma actualParisiFullSusceptibilitySquareExpected_interval_post
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0)
    (hVS : parisiEquilibriumPhysicalEndpoint β ≤ S) (hST : S ≤ T) :
    (∫ v in (S:ℝ)..T,actualParisiFullSusceptibilitySquareExpected W β v)=
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  let V := parisiEquilibriumPhysicalEndpoint β
  have he : (∫ v in (S:ℝ)..T,actualParisiFullSusceptibilitySquareExpected W β v)=
      ∫ v in (S:ℝ)..T,actualParisiContinuationR W β (v-(V:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (NNReal.coe_le_coe.mpr hST)] at hv
    have hv0 := S.coe_nonneg.trans hv.1
    have hVv : V ≤ v.toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal v hv0]
      exact (NNReal.coe_le_coe.mpr hVS).trans hv.1
    have H := actualParisiFullSusceptibilitySquareExpected_post W β hβ v.toNNReal hVv
    rw [NNReal.coe_sub hVv] at H
    simpa only [Real.coe_toNNReal v hv0] using H
  rw [he,intervalIntegral.integral_comp_sub_right]
  have hs : V+(S-V)=S := add_tsub_cancel_of_le hVS
  have ht : V+(T-V)=T := add_tsub_cancel_of_le (hVS.trans hST)
  have hsc : ((S-V:ℝ≥0):ℝ)=(S:ℝ)-(V:ℝ) := NNReal.coe_sub hVS
  have htc : ((T-V:ℝ≥0):ℝ)=(T:ℝ)-(V:ℝ) := NNReal.coe_sub (hVS.trans hST)
  rw [actualParisiContinuationP_variance_balance W β hβ _ _
    (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hVS))
    (sub_le_sub_right (NNReal.coe_le_coe.mpr hST) _)]
  have HPs := actualParisiFullOverlap_post W β hβ (S-V)
  have HPt := actualParisiFullOverlap_post W β hβ (T-V)
  rw [hs,hsc] at HPs
  rw [ht,htc] at HPt
  rw [HPs,HPt]
  ring

theorem actualParisiFullSusceptibilitySquareExpected_interval
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ v in (S:ℝ)..T,actualParisiFullSusceptibilitySquareExpected W β v)=
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  let V := parisiEquilibriumPhysicalEndpoint β
  by_cases hTV : T ≤ V
  · exact actualParisiFullSusceptibilitySquareExpected_interval_pre W β hβ S T hST hTV
  have hVT : V ≤ T := (lt_of_not_ge hTV).le
  by_cases hVS : V ≤ S
  · exact actualParisiFullSusceptibilitySquareExpected_interval_post W β hβ S T hVS hST
  have hSV : S ≤ V := (lt_of_not_ge hVS).le
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable (S:ℝ) V)
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable (V:ℝ) T),
    actualParisiFullSusceptibilitySquareExpected_interval_pre W β hβ S V hSV le_rfl,
    actualParisiFullSusceptibilitySquareExpected_interval_post W β hβ V T le_rfl hVT]
  ring

theorem actualParisiPosteriorIntervalScale_eq_sqrt_integral
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T : ℝ≥0) (hST : S < T) :
    (actualParisiPosteriorIntervalScale W β S T:ℝ)=
      Real.sqrt (∫ v in (S:ℝ)..T,actualParisiFullSusceptibilitySquareExpected W β v) := by
  rw [actualParisiFullSusceptibilitySquareExpected_interval W β hβ S T hST.le]
  rw [← actualParisiPosteriorIntervalScale_sq W β hβ S T hST,
    Real.sqrt_sq_eq_abs,abs_of_nonneg (actualParisiPosteriorIntervalScale W β S T).coe_nonneg]

end SKConstants
