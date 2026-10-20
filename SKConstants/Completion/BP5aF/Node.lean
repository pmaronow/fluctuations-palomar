module

public import SKConstants.Completion.Blueprint5a.All

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.BP5aF
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint5a

theorem supportFieldTargetMeasurable_holds : SupportFieldTargetMeasurableStatement := by
  intro Ω A _ _ W Z β hβ
  have hp : Measurable (LJ.supportPotentialPrimitive W β) := by
    unfold LJ.supportPotentialPrimitive
    simp_rw [LJ.support_potential_value β hβ]
    have hy : Measurable (fun u : Bool × Ω => actualParisiFullScalarProcess W β
        (parisiEquilibriumPhysicalEndpoint β) u.2) :=
      (measurable_actualParisiPreContinuationField W β _).comp measurable_snd
    have ha := LJ.measurable_actualRowPotential W β (parisiEquilibriumPhysicalEndpoint β)
    have hs : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1) :=
      (measurable_of_finite scalarHiddenSign).comp measurable_fst
    fun_prop
  exact (hp.comp measurable_fst).sub
    (((SJ3.measurable_potentialIntegral W β hβ (parisiEquilibriumPhysicalEndpoint β)).comp
      measurable_fst).const_mul (β ^ 2))

theorem postSupportProfile_holds : PostSupportProfileStatement := by
  intro Ω _ W β hβ V hV
  let S := parisiEquilibriumPhysicalEndpoint β
  have hp (t : ℝ≥0) (ht : S ≤ t) :
      actualParisiFullSusceptibilityExpected W β t = 1 - actualParisiFullOverlap W β t := by
    have ho := actualParisiFullOverlap_post W β hβ (t - S)
    rw [add_tsub_cancel_of_le ht, NNReal.coe_sub ht] at ho
    have he := actualParisiFullSusceptibilityExpected_post W β hβ
      ((t : ℝ) - S) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht))
    rw [add_sub_cancel] at he
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [actualParisiFullSusceptibilitySquareExpected_interval_post W β hβ S V le_rfl hV,
      hp S le_rfl, hp V hV]
    ring
  · exact (continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable _ _
  · intro u
    have hm : Measurable (fun t : ℝ => LJ.actualRowPotential W β t.toNNReal u) :=
      (SJ3.measurable_actualRowPotential_time W β).comp (measurable_const.prodMk measurable_id)
    have hr := continuous_actualParisiFullSusceptibilitySquareExpected W β
    apply ((hr.abs.const_mul 2).intervalIntegrable (S : ℝ) V).mono_fun
      (hm.mul hr.measurable).aestronglyMeasurable
    filter_upwards [] with t
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right (SJ3.actualRowPotential_bound W β t.toNNReal u) (abs_nonneg _)

theorem jointEndpointIdentity_of_original_subnodes (h1 : QueryRowIntegralExistsStatement)
    (h2a : PreSupportQueryDriverStatement) (h2b : SupportFieldItoStatement)
    (h3a : PostSupportInformationItoStatement) (h3b : PostSupportPotentialStatement) :
    Blueprint4.JointEndpointIdentityStatement :=
  Blueprint5a.jointEndpointIdentity_of_subnodes h1 h2a h2b supportFieldTargetMeasurable_holds
    h3a h3b postSupportProfile_holds

theorem sharpRowConcentration_of_original_subnodes (h31 : QueryRowIntegralExistsStatement)
    (h32a : PreSupportQueryDriverStatement) (h32b : SupportFieldItoStatement)
    (h33a : PostSupportInformationItoStatement) (h33b : PostSupportPotentialStatement)
    (h71 : RefinedResidualLimitStatement) (h73 : QuadraticGroupLimitStatement)
    (h74a : SignSymmetrizationStatement) (h74b : LinearGroupSubgaussianStatement)
    (h75 : PredictableGroupMGFStatement) (h76 : LagGroupMGFStatement) :
    Blueprint4.SharpRowConcentrationStatement :=
  Blueprint5a.sharpRowConcentration_of_subnodes h31 h32a h32b supportFieldTargetMeasurable_holds
    h33a h33b postSupportProfile_holds h71 h73 h74a h74b h75 h76

end SKConstants.Completion.BP5aF
