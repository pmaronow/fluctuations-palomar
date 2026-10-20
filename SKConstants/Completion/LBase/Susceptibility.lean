module

public import SKConstants.Completion.LQ.ActualProfileBounds
public import SKConstants.ParisiEquilibriumLocking
public import SKConstants.ParisiCDFBrownianLaw

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_susceptibility_pre_average (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : v ∈ Icc 0 (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    actualParisiFullSusceptibilityExpected W β v =
      scalarCDFSusceptibilityAverage β (cdf (parisiEquilibriumMeasure β : Measure ℝ))
        (v / β^2) := by
  have hp : 0 < β := zero_lt_one.trans hβ
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ)
  have ha : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have h1 : α 1 = 1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hv' : v ∈ Icc 0 (β^2 * parisiEquilibriumSupportEndpoint β) := by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using hv
  have hq := parisiPhysicalTime_mem_unit β hβ hv'
  have hqQ : v / β^2 ≤ parisiEquilibriumSupportEndpoint β :=
    (div_le_iff₀ (sq_pos_of_pos hp)).mpr (by simpa only [mul_comm] using hv'.2)
  have hq1 : v / β^2 < 1 :=
    hqQ.trans_lt (parisiEquilibriumSupportEndpoint_spec β hβ).1.2
  have H := scalarCDFAverage_eq_actualBrownian_expectation W β hp α ha h1
    ⟨hq.1, hq1⟩ (scalarCDFHessian_boundedSmooth β hp.ne' α ha ⟨hq.1, hq1⟩)
  rw [mul_div_cancel₀ v (pow_ne_zero 2 hp.ne')] at H
  rw [actualParisiFullSusceptibilityExpected_pre W β hβ ha h1 hv']
  exact H.symm

theorem actual_susceptibility_pre_area (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (v : ℝ) (hv : v ∈ Icc 0 (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    actualParisiFullSusceptibilityExpected W β v =
      ∫ q in (v / β^2)..1, cdf (parisiEquilibriumMeasure β : Measure ℝ) q := by
  rw [actual_susceptibility_pre_average W β hβ v hv]
  apply parisiEquilibrium_susceptibility_on_support β (zero_lt_one.trans hβ).ne'
  rw [(parisiEquilibrium_full_support W β hβ).1]
  refine ⟨div_nonneg hv.1 (sq_nonneg β), ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos (zero_lt_one.trans hβ))).mpr
  simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ, mul_comm] using hv.2

theorem actual_susceptibility_pre_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ)
    (hv : 0 ≤ v) (hvend : v < (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    HasDerivWithinAt (actualParisiFullSusceptibilityExpected W β)
      (-cdf (parisiEquilibriumMeasure β : Measure ℝ) (v / β^2) / β^2) (Ioi v) v := by
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ)
  have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have HD : HasDerivWithinAt (fun x : ℝ => ∫ q in x..1, α q)
      (-α (v / β^2)) (Ici (v / β^2)) (v / β^2) :=
    intervalIntegral.integral_hasDerivWithinAt_left (α.mono.intervalIntegrable (μ := volume))
      α.mono.measurable.stronglyMeasurable.stronglyMeasurableAtFilter
      ((α.right_continuous _).mono Ioi_subset_Ici_self)
  have hc : HasDerivWithinAt (fun x : ℝ => ∫ q in (x / β^2)..1, α q)
      (-α (v / β^2) / β^2) (Ioi v) v := by
    convert HD.comp v (((hasDerivAt_id v).div_const (β^2)).hasDerivWithinAt)
      (fun x (hx : x ∈ Ioi v) => div_le_div_of_nonneg_right hx.le hb.le) using 1 <;>
      simp only [div_eq_mul_inv, one_mul, Function.comp_def, id_eq]
  have he : (fun x : ℝ => ∫ q in (x / β^2)..1, α q) =ᶠ[𝓝[>] v]
      actualParisiFullSusceptibilityExpected W β := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hvend)] with x hx hxend
    exact (actual_susceptibility_pre_area W β hβ x ⟨hv.trans hx.le, hxend.le⟩).symm
  have HH := hc.congr_of_eventuallyEq he.symm
    (actual_susceptibility_pre_area W β hβ v ⟨hv, hvend.le⟩)
  simpa only [div_eq_mul_inv, one_mul, α] using HH

theorem actual_square_profile_le_susceptibility (W : BrownianSystem Ω) (β v : ℝ) :
    actualParisiFullSusceptibilitySquareExpected W β v ≤
      actualParisiFullSusceptibilityExpected W β v := by
  apply integral_mono (actualParisiFullCurvatureObservable_sq_integrable W β v)
    (actualParisiFullCurvatureObservable_integrable W β v)
  intro w
  have ha := (actualParisiFullMagnetization_curvature_bounds β v
    (actualParisiFullScalarProcess W β v.toNNReal w)).2.1
  have hb := actualParisiFullCurvature_abs_le_one β v
    (actualParisiFullScalarProcess W β v.toNNReal w)
  rw [abs_of_nonneg ha] at hb
  nlinarith

theorem actual_susceptibility_pre_derivative_bound
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (v : ℝ)
    (hv : 0 ≤ v) (hvend : v ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    |-cdf (parisiEquilibriumMeasure β : Measure ℝ) (v / β^2) / β^2| ≤
      actualParisiFullSusceptibilityExpected W β v := by
  have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have hpre := actualParisiFullSusceptibilitySquareExpected_pre W β hβ v.toNNReal
    (by apply NNReal.coe_le_coe.mp; simpa only [Real.coe_toNNReal v hv] using hvend)
  rw [Real.coe_toNNReal v hv] at hpre
  have H := actual_square_profile_le_susceptibility W β v
  rw [hpre] at H
  calc
    _ = cdf (parisiEquilibriumMeasure β : Measure ℝ) (v / β^2) / β^2 := by
      rw [abs_div, abs_neg, abs_of_nonneg (cdf_nonneg _ _), abs_of_pos hb]
    _ ≤ 1 / β^2 := div_le_div_of_nonneg_right (cdf_le_one _ _) hb.le
    _ ≤ _ := H

end SKConstants.Completion.LBase
