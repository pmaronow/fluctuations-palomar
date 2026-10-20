module

public import SKConstants.Completion.Blueprint5a.Statements
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SKConstants.Completion.S33b
open SKConstantsOAI.ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

theorem stieltjes_restrict_Ioi_eq_withDensity (f : StieltjesFunction ℝ)
    (g : ℝ → ℝ) (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) (s : ℝ)
    (hfg : ∀ a b, s ≤ a → a ≤ b → f b - f a = ∫ t in a..b, g t) :
    f.measure.restrict (Ioi s) =
      (volume.withDensity (fun t => ENNReal.ofReal (g t))).restrict (Ioi s) := by
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [Measure.restrict_apply measurableSet_Ioc,
    Measure.restrict_apply measurableSet_Ioc, Ioc_inter_Ioi]
  by_cases h : max a s ≤ b
  · rw [f.measure_Ioc, hfg _ _ (le_max_right _ _) h,
      withDensity_apply _ measurableSet_Ioc,
      intervalIntegral.integral_of_le h]
    exact ofReal_integral_eq_lintegral_ofReal
      ((hg.intervalIntegrable _ _).1) (ae_of_all _ hg0)
  · simp only [Ioc_eq_empty_of_le (le_of_lt (lt_of_not_ge h)), measure_empty]

theorem susceptibility_post_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ) (hS : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ S) (hST : S ≤ T) :
    actualParisiFullSusceptibilityExpected W β S -
        actualParisiFullSusceptibilityExpected W β T =
      ∫ t in S..T, actualParisiFullSusceptibilitySquareExpected W β t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hST
    (continuous_actualParisiFullSusceptibilityExpected W β).continuousOn
    (fun t ht => LBase.actual_susceptibility_post_hasDerivWithinAt_right W β hβ t
      (hS.trans ht.1.le))
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).neg.intervalIntegrable S T)
  simp only [intervalIntegral.integral_neg] at h
  linarith

theorem negativeSusceptibility_measure_post (W : BrownianSystem Ω) (β : ℝ)
    (hβ : 1 < β) :
    (SJ3.negativeSusceptibility W β hβ).measure.restrict
        (Ioi (parisiEquilibriumPhysicalEndpoint β : ℝ)) =
      (volume.withDensity (fun t =>
        ENNReal.ofReal (actualParisiFullSusceptibilitySquareExpected W β t))).restrict
          (Ioi (parisiEquilibriumPhysicalEndpoint β : ℝ)) := by
  apply stieltjes_restrict_Ioi_eq_withDensity
    (SJ3.negativeSusceptibility W β hβ)
    (actualParisiFullSusceptibilitySquareExpected W β)
    (continuous_actualParisiFullSusceptibilitySquareExpected W β)
    (fun t => (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1)
  intro a b ha hab
  have ha0 := (parisiEquilibriumPhysicalEndpoint β).coe_nonneg.trans ha
  have hb0 := ha0.trans hab
  simpa only [SJ3.negativeSusceptibility, Real.coe_toNNReal a ha0,
    Real.coe_toNNReal b hb0, neg_sub_neg] using
    susceptibility_post_integral W β hβ a b ha hab

theorem postSupport_stieltjes_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ) (hS : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ S) (hST : S ≤ T)
    (F : ℝ → ℝ) :
    (∫ t in S..T, F t ∂(SJ3.negativeSusceptibility W β hβ).measure) =
      ∫ t in S..T, F t * actualParisiFullSusceptibilitySquareExpected W β t := by
  have hs : Ioc S T ⊆ Ioi (parisiEquilibriumPhysicalEndpoint β : ℝ) :=
    fun t ht => hS.trans_lt ht.1
  have hm := congrArg (fun μ : Measure ℝ => μ.restrict (Ioc S T))
    (negativeSusceptibility_measure_post W β hβ)
  simp only [Measure.restrict_restrict_of_subset hs] at hm
  rw [intervalIntegral.integral_of_le hST, intervalIntegral.integral_of_le hST]
  change (∫ t, F t ∂((SJ3.negativeSusceptibility W β hβ).measure.restrict (Ioc S T))) = _
  rw [hm]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (continuous_actualParisiFullSusceptibilitySquareExpected W β).measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) F measurableSet_Ioc]
  simp only [ENNReal.toReal_ofReal (actualParisiFullSusceptibilitySquareExpected_bounds W β _).1,
    smul_eq_mul, mul_comm]

theorem actualRowPotential_intervalIntegrable_stieltjes (W : BrownianSystem Ω) (β : ℝ)
    (u : Bool × Ω) (f : StieltjesFunction ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t => LJ.actualRowPotential W β t.toNNReal u) f.measure a b := by
  apply intervalIntegrable_iff.mpr
  let : IsFiniteMeasure (f.measure.restrict (uIoc a b)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [uIoc, f.measure_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hm : Measurable (fun t : ℝ => LJ.actualRowPotential W β t.toNNReal u) :=
    (SJ3.measurable_actualRowPotential_time W β).comp (measurable_const.prodMk measurable_id)
  exact Integrable.of_bound hm.aestronglyMeasurable 2
    (ae_of_all _ (fun t => by
      simpa only [Real.norm_eq_abs] using SJ3.actualRowPotential_bound W β t.toNNReal u))

theorem actualRowPotential_mul_square_intervalIntegrable (W : BrownianSystem Ω) (β : ℝ)
    (u : Bool × Ω) (a b : ℝ) :
    IntervalIntegrable (fun t => LJ.actualRowPotential W β t.toNNReal u *
      actualParisiFullSusceptibilitySquareExpected W β t) volume a b := by
  have hA : IntervalIntegrable (fun t => LJ.actualRowPotential W β t.toNNReal u)
      volume a b := by
    apply intervalIntegrable_iff.mpr
    let : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
      isFiniteMeasure_restrict.mpr (by simp [uIoc])
    have hm : Measurable (fun t : ℝ => LJ.actualRowPotential W β t.toNNReal u) :=
      (SJ3.measurable_actualRowPotential_time W β).comp (measurable_const.prodMk measurable_id)
    exact Integrable.of_bound hm.aestronglyMeasurable 2
      (ae_of_all _ (fun t => by
        simpa only [Real.norm_eq_abs] using SJ3.actualRowPotential_bound W β t.toNNReal u))
  exact hA.mul_continuousOn
    (continuous_actualParisiFullSusceptibilitySquareExpected W β).continuousOn

theorem potentialIntegral_sub_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hS : parisiEquilibriumPhysicalEndpoint β ≤ S) (hST : S ≤ T)
    (u : Bool × Ω) :
    SJ3.potentialIntegral W β hβ T u - SJ3.potentialIntegral W β hβ S u =
      actualParisiFullSusceptibilityExpected W β T * LJ.actualRowPotential W β T u -
        actualParisiFullSusceptibilityExpected W β S * LJ.actualRowPotential W β S u +
      ∫ t in (S : ℝ)..(T : ℝ), LJ.actualRowPotential W β t.toNNReal u *
        actualParisiFullSusceptibilitySquareExpected W β t := by
  have hdiff := intervalIntegral.integral_interval_sub_left
    (actualRowPotential_intervalIntegrable_stieltjes W β u
      (SJ3.negativeSusceptibility W β hβ) 0 T)
    (actualRowPotential_intervalIntegrable_stieltjes W β u
      (SJ3.negativeSusceptibility W β hβ) 0 S)
  rw [postSupport_stieltjes_integral W β hβ _ _ (NNReal.coe_le_coe.mpr hS)
    (NNReal.coe_le_coe.mpr hST)] at hdiff
  unfold SJ3.potentialIntegral
  linarith

theorem postSupportPotential_holds : Blueprint5a.PostSupportPotentialStatement := by
  intro Ω _ W β hβ V hV u
  exact potentialIntegral_sub_post W β hβ _ V le_rfl hV u

end SKConstants.Completion.S33b
