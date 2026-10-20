module
public import SKConstants.Completion.LJ.EndpointMatching
public import SKConstants.ParisiCDFCurvatureMoments
public import SKConstants.ParisiActualRestartCoordinate
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

theorem susceptibility_eq_jet_expected (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {T : ℝ} (hQT : parisiEquilibriumSupportEndpoint β < T) (hT0 : 0 ≤ T) (hT1 : T < 1)
    (v : ℝ≥0) (hv : v ≤ parisiEquilibriumPhysicalEndpoint β) :
    actualParisiFullSusceptibilityExpected W β v =
      (physicalCDFJetField β (cdf (parisiEquilibriumMeasure β : Measure ℝ))
        (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
        (supported_probability_cdf_one (parisiEquilibriumMeasure β)
          (parisiEquilibriumMeasure_upstream_spec β).1)
        (zero_lt_one.trans hβ).ne' hT0 hT1 1).expected (actualParisiFullScalarDrift β) W v := by
  unfold actualParisiFullSusceptibilityExpected TimeField.expected
  simp only [Real.toNNReal_coe]
  apply integral_congr_ae
  apply ae_of_all
  intro w
  change actualParisiFullCurvature β v (actualParisiFullScalarProcess W β v w) = _
  rw [actualParisiFullCurvature_eq_compact_before_support β hβ hQT hT0 hT1 v hv]
  dsimp only [physicalCDFJetField, rescaleTimeField, compactCDFJetField]
  rw [show (1 / β ^ 2) * (v : ℝ) = (v : ℝ) / β ^ 2 by ring]
  rfl

theorem susceptibility_pre_right_derivative (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ≥0) (hv : v < parisiEquilibriumPhysicalEndpoint β) :
    HasDerivWithinAt (actualParisiFullSusceptibilityExpected W β)
      (-cdf (parisiEquilibriumMeasure β : Measure ℝ) ((v : ℝ) / β ^ 2) / β ^ 2)
      (Ioi (v : ℝ)) v := by
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ)
  let ha : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  let h1 : α 1 = 1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  let T := (parisiEquilibriumSupportEndpoint β + 1) / 2
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hT0 : 0 ≤ T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T < 1 := by dsimp [T]; linarith [hQ.2]
  have hQT : parisiEquilibriumSupportEndpoint β < T := by dsimp [T]; linarith [hQ.2]
  let F := physicalCDFJetField β α ha h1 hb hT0 hT1 1
  have htime : (v : ℝ) / β ^ 2 ∈ Icc (0 : ℝ) T := by
    refine ⟨div_nonneg v.coe_nonneg (sq_nonneg β), ?_⟩
    apply (div_le_iff₀ (sq_pos_of_ne_zero hb)).mpr
    have hv' : (v : ℝ) < β ^ 2 * parisiEquilibriumSupportEndpoint β := by
      simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_lt_coe.mpr hv
    nlinarith [mul_lt_mul_of_pos_left hQT (sq_pos_of_ne_zero hb)]
  have hgen (x : ℝ) : F.generator (actualParisiFullScalarDrift β).f v x =
      -α ((v : ℝ) / β ^ 2) * (actualParisiFullCurvature β v x) ^ 2 := by
    have he : (actualParisiFullScalarDrift β).f v = physicalCDFCompactDrift β α T v :=
      funext (finiteTemperatureCDFDrift_eq_compact β α ha h1 hb hT1.le htime)
    have hegen : F.generator (actualParisiFullScalarDrift β).f v x =
        F.generator (physicalCDFCompactDrift β α T) v x := by
      unfold TimeField.generator
      rw [he]
    rw [hegen]
    change (physicalCDFJetField β α ha h1 hb hT0 hT1 1).generator _ _ _ = _
    rw [physicalCDFJetField_generator_one β α ha h1 hb hT0 hT1,
      actualParisiFullCurvature_eq_compact_before_support β hβ hQT hT0 hT1 v hv.le]
    simp only [compactCDFCoefficient, cdfStripTime_eq htime]
    rfl
  have hvH : (v : ℝ) < T / (1 / β ^ 2) := by
    simp only [one_div, div_inv_eq_mul]
    have hval := NNReal.coe_lt_coe.mpr hv
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ] at hval
    nlinarith [mul_lt_mul_of_pos_left hQT (sq_pos_of_ne_zero hb)]
  have hd := F.expected_hasDerivWithinAt_right (actualParisiFullScalarDrift β) W v hvH
    ((finiteTemperatureCDFDrift_path_right_continuous W β α ha h1).mono (fun w hw => hw v))
  have he : (∫ w, F.generator (actualParisiFullScalarDrift β).f v
      ((actualParisiFullScalarDrift β).solution W.driver v w) ∂W.law) =
      -α ((v : ℝ) / β ^ 2) / β ^ 2 := by
    simp_rw [hgen]
    rw [integral_const_mul]
    have hr := actualParisiFullSusceptibilitySquareExpected_pre W β hβ v hv.le
    unfold actualParisiFullSusceptibilitySquareExpected at hr
    simp only [Real.toNNReal_coe] at hr
    change -α ((v : ℝ) / β ^ 2) * (∫ w, (actualParisiFullCurvature β v
      (actualParisiFullScalarProcess W β v w)) ^ 2 ∂W.law) = _
    rw [hr]
    ring
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  · have hevent : Iio (parisiEquilibriumPhysicalEndpoint β : ℝ) ∈ 𝓝[Ioi (v : ℝ)] (v : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (NNReal.coe_lt_coe.mpr hv))
    filter_upwards [hevent, self_mem_nhdsWithin] with r hrS hrv
    have hr0 : 0 ≤ r := v.coe_nonneg.trans hrv.le
    have hr : r.toNNReal ≤ parisiEquilibriumPhysicalEndpoint β := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal r hr0]
      exact hrS.le
    simpa only [Real.coe_toNNReal r hr0] using
      susceptibility_eq_jet_expected W β hβ hQT hT0 hT1 r.toNNReal hr
  · exact susceptibility_eq_jet_expected W β hβ hQT hT0 hT1 v hv.le

theorem susceptibility_pre_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    (∫ v in 0..(parisiEquilibriumPhysicalEndpoint β : ℝ), actualParisiFullSusceptibilityExpected W β v) =
      (parisiEquilibriumPhysicalEndpoint β : ℝ) *
        actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β) +
      (∫ v in 0..(parisiEquilibriumPhysicalEndpoint β : ℝ),
        cdf (parisiEquilibriumMeasure β : Measure ℝ) (v / β ^ 2) * (v / β ^ 2)) := by
  let S := parisiEquilibriumPhysicalEndpoint β
  let p := actualParisiFullSusceptibilityExpected W β
  let g : ℝ → ℝ := fun v => cdf (parisiEquilibriumMeasure β : Measure ℝ) (v / β ^ 2) * (v / β ^ 2)
  have hp : Continuous p := continuous_actualParisiFullSusceptibilityExpected W β
  have hg : IntervalIntegrable g volume 0 S :=
    parisiPhysicalOverlapPenalty_intervalIntegrable β (parisiEquilibriumMeasure β) 0 S
  have hd (v : ℝ) (hv : v ∈ Ioo 0 (S : ℝ)) :
      HasDerivWithinAt (fun r => r * p r) (p v - g v) (Ioi v) v := by
    have hvS : v.toNNReal < S := by
      apply NNReal.coe_lt_coe.mp
      rw [Real.coe_toNNReal v hv.1.le]
      exact hv.2
    have hdp := susceptibility_pre_right_derivative W β hβ v.toNNReal hvS
    rw [Real.coe_toNNReal v hv.1.le] at hdp
    convert (hasDerivWithinAt_id v (Ioi v)).mul hdp using 1
    · rfl
    · dsimp [p, g]
      ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le S.coe_nonneg
    (continuous_id.mul hp).continuousOn hd ((hp.intervalIntegrable 0 S).sub hg)
  rw [intervalIntegral.integral_sub (hp.intervalIntegrable 0 S) hg] at hh
  simp only [Pi.mul_apply, id_eq, zero_mul, sub_zero] at hh
  dsimp only [p, g, S] at hh
  linarith

theorem energy_pressure_normalization_support (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    β * actualParisiEnergyReference W β (parisiEquilibriumPhysicalEndpoint β) +
      (β ^ 2 / 2) * (actualParisiFullSusceptibilityExpected W β
        (parisiEquilibriumPhysicalEndpoint β)) ^ 2 =
      2 * (parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0 -
        parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ))) := by
  have he := actualParisiEnergyReference_pre W β hβ
  rw [susceptibility_pre_integral W β hβ] at he
  have hp := actualParisiFullSusceptibilityExpected_post W β hβ 0 le_rfl
  simp only [add_zero] at hp
  rw [actualParisiContinuationP_zero W β hβ] at hp
  have hc := parisiEquilibrium_physical_pressure_cancellation β hβ
  rw [hp, parisiEquilibriumPhysicalEndpoint_coe β hβ] at he ⊢
  nlinarith [hc]

theorem energy_pressure_normalization (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ) (hV : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ V) :
    β * actualParisiEnergyReference W β V +
      (β ^ 2 / 2) * (actualParisiFullSusceptibilityExpected W β V) ^ 2 =
      2 * (parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0 -
        parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ))) := by
  have hh := energy_pressure_normalization_support W β hβ
  have he := actualParisiEnergyReference_post_increment W β hβ
    (V - (parisiEquilibriumPhysicalEndpoint β : ℝ)) (sub_nonneg.mpr hV)
  have hp := actualParisiFullSusceptibilityExpected_post W β hβ
    (V - (parisiEquilibriumPhysicalEndpoint β : ℝ)) (sub_nonneg.mpr hV)
  rw [add_sub_cancel] at he hp
  have hi := actualParisiContinuationRP_square_balance W β hβ
    (V - (parisiEquilibriumPhysicalEndpoint β : ℝ)) (sub_nonneg.mpr hV)
  rw [hi, actualParisiContinuationP_zero W β hβ] at he
  have hp0 := actualParisiFullSusceptibilityExpected_post W β hβ 0 le_rfl
  simp only [add_zero] at hp0
  rw [actualParisiContinuationP_zero W β hβ] at hp0
  rw [hp0] at hh
  rw [he, hp]
  nlinarith [hh]

theorem supportPotential_pressure_matching (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (u : Bool × Ω) :
    Real.log (actualParisiFullTerminalSpinDensity β W (parisiEquilibriumPhysicalEndpoint β) u) -
      (supportPotentialPrimitive W β u -
        β * actualParisiEnergyReference W β (parisiEquilibriumPhysicalEndpoint β) / 2) =
      Real.log 2 - parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) -
        β ^ 2 * (actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β)) ^ 2 / 4 +
        (β ^ 2 * actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β) / 2) *
          actualParisiPinningError W β (parisiEquilibriumPhysicalEndpoint β) u := by
  have hm := supportPotential_matching W β hβ u
  have hn := energy_pressure_normalization_support W β hβ
  linarith

end SKConstants.Completion.LJ
