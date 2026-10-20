module

public import SKConstants.Completion.LBase.TerminalProfile

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_susceptibility_post_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℝ)
    (ht : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ t) :
    HasDerivWithinAt (actualParisiFullSusceptibilityExpected W β)
      (-actualParisiFullSusceptibilitySquareExpected W β t) (Ioi t) t := by
  let E : ℝ := parisiEquilibriumPhysicalEndpoint β
  have hv : 0 ≤ t - E := sub_nonneg.mpr ht
  have H := actualParisiContinuationP_hasDerivWithinAt_right W β hβ (t - E) hv
  have hc : HasDerivWithinAt (fun x : ℝ => actualParisiContinuationP W β (x - E))
      (-actualParisiContinuationR W β (t - E)) (Ioi t) t := by
    convert H.comp t (((hasDerivAt_id t).sub_const E).hasDerivWithinAt)
      (fun x (hx : x ∈ Ioi t) => sub_lt_sub_right (show t < x from hx) E) using 1 <;>
      simp only [mul_one, Function.comp_def, id_eq]
  have hp (x : ℝ) (hx : E ≤ x) :
      actualParisiFullSusceptibilityExpected W β x = actualParisiContinuationP W β (x - E) := by
    have hh := actualParisiFullSusceptibilityExpected_post W β hβ (x - E) (sub_nonneg.mpr hx)
    simpa only [add_sub_cancel, E] using hh
  have he : (fun x : ℝ => actualParisiContinuationP W β (x - E)) =ᶠ[𝓝[>] t]
      actualParisiFullSusceptibilityExpected W β := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hp x (ht.trans hx.le)).symm
  have HH := hc.congr_of_eventuallyEq he.symm (hp t ht)
  rw [LQ.actual_square_profile_eq W β hβ t ((parisiEquilibriumPhysicalEndpoint β).coe_nonneg.trans ht)]
  exact HH

theorem actual_susceptibility_hasDerivWithinAt_right
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (actualParisiFullSusceptibilityExpected W β)
      (-(cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β^2)) *
        actualParisiFullSusceptibilitySquareExpected W β t) (Ioi t) t := by
  by_cases hpre : t < (parisiEquilibriumPhysicalEndpoint β : ℝ)
  · have hr := actualParisiFullSusceptibilitySquareExpected_pre W β hβ t.toNNReal
      (by apply NNReal.coe_le_coe.mp; simpa only [Real.coe_toNNReal t ht] using hpre.le)
    rw [Real.coe_toNNReal t ht] at hr
    rw [hr]
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      actual_susceptibility_pre_hasDerivWithinAt_right W β hβ t ht hpre
  · have hpost := le_of_not_gt hpre
    have hq : parisiEquilibriumSupportEndpoint β ≤ t / β^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans hβ))).mpr
      simpa only [mul_comm, parisiEquilibriumPhysicalEndpoint_coe β hβ] using hpost
    rw [actualParisiEquilibrium_cdf_one_after_support β hβ _ hq, neg_one_mul]
    exact actual_susceptibility_post_hasDerivWithinAt_right W β hβ t hpost

theorem actual_susceptibility_antitone (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    AntitoneOn (actualParisiFullSusceptibilityExpected W β) (Ici 0) := by
  intro s hs t ht hst
  have HD : ∀ x ∈ Ico s t, HasDerivWithinAt (actualParisiFullSusceptibilityExpected W β)
      (-(cdf (parisiEquilibriumMeasure β : Measure ℝ) (x / β^2)) *
        actualParisiFullSusceptibilitySquareExpected W β x) (Ici x) x := by
    intro x hx
    exact (actual_susceptibility_hasDerivWithinAt_right W β hβ x (hs.trans hx.1)).Ici_of_Ioi
  have H := image_le_of_deriv_right_le_deriv_boundary
    (continuous_actualParisiFullSusceptibilityExpected W β).continuousOn HD
    (B := fun _ => actualParisiFullSusceptibilityExpected W β s) (B' := fun _ => 0) (by rfl)
    continuous_const.continuousOn (fun x _ => hasDerivWithinAt_const _ _ _) (by
      intro x hx
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (cdf_nonneg _ _))
        (actualParisiFullSusceptibilitySquareExpected_bounds W β x).1)
  exact H ⟨hst, le_rfl⟩

theorem actual_susceptibility_derivative_bound (W : BrownianSystem Ω) (β t : ℝ) :
    |-(cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β^2)) *
        actualParisiFullSusceptibilitySquareExpected W β t| ≤
      actualParisiFullSusceptibilityExpected W β t := by
  rw [abs_mul, abs_neg, abs_of_nonneg (cdf_nonneg _ _),
    abs_of_nonneg (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1]
  exact (mul_le_of_le_one_left (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1
    (cdf_le_one _ _)).trans (actual_square_profile_le_susceptibility W β t)

theorem actual_square_profile_le_inverse_beta_sq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : 0 ≤ t) : actualParisiFullSusceptibilitySquareExpected W β t ≤ 1 / β^2 := by
  rw [LQ.actual_square_profile_eq W β hβ t ht]
  exact actualParisiContinuationR_le_inverse_beta_sq W β hβ _

end SKConstants.Completion.LBase
