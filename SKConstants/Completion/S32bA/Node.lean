module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.Completion.S32bA.Quadratic
public import SKConstants.ScalarProcessLogCosh

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace SKConstants.Completion.S32bA
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.ZeroTemperatureSK.Heat
  SKConstantsOAI.SK.Analytic ParisiFullSupport Blueprint5a

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem fullScalar_integral_equation (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, ∀ t : ℝ≥0,
      actualParisiFullScalarProcess W β t w = W.B t w +
        ∫ s in (0 : ℝ)..(t : ℝ),
          (actualParisiFullScalarDrift β).f s.toNNReal
            (actualParisiFullScalarProcess W β s.toNNReal w) := by
  filter_upwards [W.driver_indistinguishable] with w hw
  intro t
  rw [actualParisiFullScalarProcess,
    BoundedLipschitzDrift.solution_eq _ _ W.driver_progressive, hw]

theorem fullScalar_integral_equation_base (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) :
    ∀ᵐ u ∂LM4.actualRowBaseLaw W Z, ∀ t : ℝ≥0,
      actualParisiFullScalarProcess W β t u.1.2 = W.B t u.1.2 +
        ∫ s in (0 : ℝ)..(t : ℝ),
          (actualParisiFullScalarDrift β).f s.toNNReal
            (actualParisiFullScalarProcess W β s.toNNReal u.1.2) := by
  let := W.isProbability
  let := Z.isProbability
  exact (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
      (ν := Z.law)).quasiMeasurePreserving.ae
    ((measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).quasiMeasurePreserving.ae
      (fullScalar_integral_equation W β))

theorem drift_eq_pre (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (y : ℝ) :
    (actualParisiFullScalarDrift β).f t y =
      cdf (parisiEquilibriumMeasure β : Measure ℝ) ((t : ℝ) / β ^ 2) *
        actualParisiFullMagnetization β t y := by
  have hb : 0 < β ^ 2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have hq := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have ht' := NNReal.coe_le_coe.mpr ht
  rw [parisiEquilibriumPhysicalEndpoint_coe β hβ] at ht'
  have hdiv : (t : ℝ) / β ^ 2 ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg t.coe_nonneg hb.le,
      ((div_le_iff₀ hb).mpr (by simpa only [mul_comm] using ht')).trans hq.2.le⟩
  change cdf _ (cdfTimeClamp ((t : ℝ) / β ^ 2)) * _ = _
  congr 1
  unfold cdfTimeClamp
  rw [min_eq_left hdiv.2, max_eq_right hdiv.1]

theorem scaled_negativeSusceptibility_right_derivative
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t < parisiEquilibriumPhysicalEndpoint β) :
    HasDerivWithinAt
      (fun s => β ^ 2 * (-actualParisiFullSusceptibilityExpected W β s))
      (cdf (parisiEquilibriumMeasure β : Measure ℝ) ((t : ℝ) / β ^ 2))
      (Ioi (t : ℝ)) t := by
  have hd := ((LJ.susceptibility_pre_right_derivative W β hβ t ht).neg).const_mul (β ^ 2)
  convert hd using 1
  field_simp

theorem susceptibility_pre_increment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    (∫ r in s..t, cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2)) =
      β ^ 2 * (actualParisiFullSusceptibilityExpected W β s -
        actualParisiFullSusceptibilityExpected W β t) := by
  have hm : Monotone (fun r : ℝ => cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2)) :=
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono.comp
      (fun _ _ h => div_le_div_of_nonneg_right h (sq_nonneg β))
  have hd (r : ℝ) (hr : r ∈ Ioo s t) :=
    scaled_negativeSusceptibility_right_derivative W β hβ r.toNNReal
      (show r.toNNReal < parisiEquilibriumPhysicalEndpoint β by
        apply NNReal.coe_lt_coe.mp
        rw [Real.coe_toNNReal r (hs.trans hr.1.le)]
        exact hr.2.trans_le ht)
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := fun r => β ^ 2 * (-actualParisiFullSusceptibilityExpected W β r)) hst
    ((continuous_const.mul (continuous_actualParisiFullSusceptibilityExpected W β).neg).continuousOn)
    (fun r hr => by
      convert! hd r hr using 1 <;>
        simp only [Real.coe_toNNReal r (hs.trans hr.1.le)])
    hm.intervalIntegrable
  simpa only [Pi.mul_apply, Pi.neg_apply, mul_neg, sub_neg_eq_add, neg_add_eq_sub,
    mul_sub] using H

theorem negativeSusceptibility_measure_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ) (hs : 0 ≤ s) (_hst : s ≤ t)
    (ht : t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)) :
    ENNReal.ofReal (β ^ 2) • ((SJ3.negativeSusceptibility W β hβ).measure.restrict (Ioc s t)) =
      (volume.withDensity (fun r => ENNReal.ofReal
        (cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2)))).restrict (Ioc s t) := by
  let f := SJ3.negativeSusceptibility W β hβ
  let α : ℝ → ℝ := fun r => cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2)
  have hm : Monotone α := (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono.comp
    (fun _ _ h => div_le_div_of_nonneg_right h (sq_nonneg β))
  let : IsFiniteMeasure
      (ENNReal.ofReal (β ^ 2) • (f.measure.restrict (Ioc s t))) := ⟨by
    rw [Measure.smul_apply, Measure.restrict_apply_univ, f.measure_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
    Measure.restrict_apply measurableSet_Ioc]
  have hinter : Ioc a b ∩ Ioc s t = Ioc (max a s) (min b t) := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  rw [hinter]
  by_cases h : max a s < min b t
  · have h0 : 0 ≤ max a s := hs.trans (le_max_right a s)
    have hS : min b t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ) := (min_le_right b t).trans ht
    have hp := susceptibility_pre_increment W β hβ (max a s) (min b t) h0 h.le hS
    have hi : IntegrableOn α (Ioc (max a s) (min b t)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le h.le).mp hm.intervalIntegrable
    rw [withDensity_apply _ measurableSet_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ (fun r => cdf_nonneg _ _)),
      ← intervalIntegral.integral_of_le h.le, hp, f.measure_Ioc, smul_eq_mul,
      ← ENNReal.ofReal_mul (sq_nonneg β)]
    congr 1
    dsimp only [f, SJ3.negativeSusceptibility]
    rw [Real.coe_toNNReal _ h0,
      Real.coe_toNNReal _ (h0.trans h.le)]
    ring
  · rw [Ioc_eq_empty_of_le (le_of_not_gt h)]
    simp

theorem negativeSusceptibility_integral_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)) (g : ℝ → ℝ) :
    β ^ 2 * (∫ r in s..t, g r ∂(SJ3.negativeSusceptibility W β hβ).measure) =
      ∫ r in s..t, cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) * g r := by
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
  have he := negativeSusceptibility_measure_pre W β hβ s t hs hst ht
  have hm : Measurable (fun r : ℝ => ENNReal.ofReal
      (cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2))) :=
    ((cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono.measurable.comp
      (measurable_id.div_const _)).ennreal_ofReal
  calc
    _ = ∫ r, g r ∂(ENNReal.ofReal (β ^ 2) •
        ((SJ3.negativeSusceptibility W β hβ).measure.restrict (Ioc s t))) := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg β), smul_eq_mul]
    _ = _ := by
      rw [he, setIntegral_withDensity_eq_setIntegral_toReal_smul hm
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) g measurableSet_Ioc]
      simp only [ENNReal.toReal_ofReal (cdf_nonneg _ _), smul_eq_mul]

theorem actualRowPotential_zero_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∀ᵐ u ∂(scalarHiddenPriorBool 0).prod W.law, LJ.actualRowPotential W β 0 u = 0 := by
  let := W.isProbability
  filter_upwards [(measurePreserving_snd (μ := scalarHiddenPriorBool 0)
      (ν := W.law)).quasiMeasurePreserving.ae
      (actualParisiMagnetizationObservable_zero_ae W β hβ)] with u hu
  change actualParisiFullPosteriorMean W β 0 u.2 = 0 at hu
  simp only [LJ.actualRowPotential, LJ.rowPotential, hu, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div, sub_zero]

omit [MeasurableSpace A] in
theorem supportFieldTarget_eq_time_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (u : (Bool × Ω) × A) :
    supportFieldTarget W β hβ u =
      scalarHiddenSign u.1.1 * actualParisiFullScalarProcess W β
          (parisiEquilibriumPhysicalEndpoint β) u.1.2 -
        parisiPhysicalValue β (parisiEquilibriumMeasure β) (parisiEquilibriumPhysicalEndpoint β)
          (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) u.1.2) +
        parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0 +
        β ^ 2 * actualParisiFullSusceptibilityExpected W β 0 * LJ.actualRowPotential W β 0 u.1 -
        ∫ t in (0 : ℝ)..(parisiEquilibriumPhysicalEndpoint β : ℝ),
          cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
            LJ.actualRowPotential W β t.toNNReal u.1 := by
  have hi := negativeSusceptibility_integral_pre W β hβ 0
    (parisiEquilibriumPhysicalEndpoint β) le_rfl
    (parisiEquilibriumPhysicalEndpoint β).coe_nonneg le_rfl
    (fun t => LJ.actualRowPotential W β t.toNNReal u.1)
  dsimp only [supportFieldTarget, LJ.supportPotentialPrimitive, SJ3.potentialIntegral]
  linear_combination -hi

def supportItoPrimitive (W : BrownianSystem Ω) (β : ℝ) (w : Ω) : ℝ :=
  parisiPhysicalValue β (parisiEquilibriumMeasure β) (parisiEquilibriumPhysicalEndpoint β)
      (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) w) -
    parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0 -
    (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..(parisiEquilibriumPhysicalEndpoint β : ℝ),
      cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
        (actualParisiFullPosteriorMean W β t.toNNReal w) ^ 2

attribute [local irreducible] actualParisiFullScalarDrift actualParisiFullMagnetization
  actualParisiFullScalarProcess actualParisiFullPosteriorMean

theorem posterior_drift_intervalIntegrable (W : BrownianSystem Ω) (β : ℝ)
    (s t : ℝ) (w : Ω) :
    IntervalIntegrable (fun r => cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) *
      actualParisiFullPosteriorMean W β r.toNNReal w) volume s t ∧
    IntervalIntegrable (fun r => cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) *
      (actualParisiFullPosteriorMean W β r.toNNReal w) ^ 2) volume s t := by
  have hm : Measurable (fun r : ℝ => actualParisiFullPosteriorMean W β r.toNNReal w) := by
    have hx : Measurable (fun r : ℝ => actualParisiFullScalarProcess W β r.toNNReal w) := by
      have h := (LC1.measurable_fullScalar_real_shift W β 0).comp
        (measurable_id.prodMk (measurable_const (a := w)))
      convert! h using 1
      simp only [Function.comp_def, id_eq, zero_add]
    have hc := (continuous_actualParisiFullMagnetization β).measurable.comp
      ((measurable_subtype_coe.comp measurable_real_toNNReal).prodMk
        hx)
    convert! hc using 1
    funext r
    unfold actualParisiFullPosteriorMean
    rfl
  have ha : Measurable (fun r : ℝ => cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2)) :=
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono.measurable.comp (measurable_id.div_const _)
  have hb (r : ℝ) : |actualParisiFullPosteriorMean W β r.toNNReal w| ≤ 1 :=
    by simpa only [actualParisiFullPosteriorMean, actualParisiMagnetizationObservable] using
      actualParisiMagnetizationObservable_abs_le W β r.toNNReal w
  constructor
  · apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun (ha.mul hm).aestronglyMeasurable
    apply ae_of_all
    intro r
    change |cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) *
      actualParisiFullPosteriorMean W β r.toNNReal w| ≤ |(1 : ℝ)|
    rw [abs_of_pos zero_lt_one, abs_mul,
      abs_of_nonneg (cdf_nonneg _ _)]
    exact (mul_le_mul (cdf_le_one _ _) (hb r) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
      (ha.mul (hm.pow_const 2)).aestronglyMeasurable
    apply ae_of_all
    intro r
    change |cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) *
      (actualParisiFullPosteriorMean W β r.toNNReal w) ^ 2| ≤ |(1 : ℝ)|
    rw [abs_of_pos zero_lt_one, abs_mul,
      abs_of_nonneg (cdf_nonneg _ _), abs_pow]
    exact (mul_le_mul (cdf_le_one _ _) (pow_le_pow_left₀ (abs_nonneg _) (hb r) 2)
      (pow_nonneg (abs_nonneg _) _) zero_le_one).trans_eq (by norm_num)

theorem supportFieldTarget_eq_itoPrimitive (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) :
    supportFieldTarget W β hβ =ᵐ[LM4.actualRowBaseLaw W Z]
      (fun u => scalarHiddenSign u.1.1 * W.B (parisiEquilibriumPhysicalEndpoint β) u.1.2 -
        supportItoPrimitive W β u.1.2) := by
  let := W.isProbability
  let := Z.isProbability
  have h0 := (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
    (ν := Z.law)).quasiMeasurePreserving.ae (actualRowPotential_zero_ae W β hβ)
  filter_upwards [fullScalar_integral_equation_base W Z β, h0] with u hu hzero
  rw [supportFieldTarget_eq_time_integral, hzero, mul_zero, add_zero]
  let S := parisiEquilibriumPhysicalEndpoint β
  have hdrift : (∫ t in (0 : ℝ)..(S : ℝ), (actualParisiFullScalarDrift β).f t.toNNReal
      (actualParisiFullScalarProcess W β t.toNNReal u.1.2)) =
      ∫ t in (0 : ℝ)..(S : ℝ),
        cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
          actualParisiFullPosteriorMean W β t.toNNReal u.1.2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le S.coe_nonneg] at ht
    have htS : t.toNNReal ≤ S := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal t ht.1]
      exact ht.2
    dsimp only
    rw [drift_eq_pre β hβ t.toNNReal htS, Real.coe_toNNReal t ht.1]
    simp only [actualParisiFullPosteriorMean, Real.coe_toNNReal t ht.1]
  have hy := hu S
  rw [hdrift] at hy
  have hi := posterior_drift_intervalIntegrable W β 0 S u.1.2
  have hA : (∫ t in (0 : ℝ)..(S : ℝ),
      cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
        LJ.actualRowPotential W β t.toNNReal u.1) =
      scalarHiddenSign u.1.1 * (∫ t in (0 : ℝ)..(S : ℝ),
        cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
          actualParisiFullPosteriorMean W β t.toNNReal u.1.2) -
      (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..(S : ℝ),
        cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
          (actualParisiFullPosteriorMean W β t.toNNReal u.1.2) ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hi.1.const_mul _) (hi.2.const_mul _)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [LJ.actualRowPotential, LJ.rowPotential]
    ring
  change scalarHiddenSign u.1.1 * actualParisiFullScalarProcess W β S u.1.2 - _ + _ - _ = _
  dsimp only [supportItoPrimitive]
  rw [hA]
  linear_combination (scalarHiddenSign u.1.1) * hy

theorem fullScalar_memLp_two (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) :
    MemLp (actualParisiFullScalarProcess W β t) 2 W.law := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  have hB : MemLp (W.driver t) 2 W.law :=
    (W.brownian.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.ae_eq
      (W.driver_indistinguishable.mono (fun _ h => (h t).symm))
  have hm : Measurable (b.correction W.driver t) :=
    (progressive_joint_measurable _ (b.correction_progressive _ W.driver_progressive)).comp
      (measurable_const.prodMk measurable_id)
  have hc : MemLp (b.correction W.driver t) 2 W.law :=
    MemLp.of_bound hm.aestronglyMeasurable ((b.bound : ℝ) * (t : ℝ))
      (ae_of_all _ (fun w => by
        simpa only [Real.norm_eq_abs] using b.correction_bound _ W.driver_progressive t w))
  convert! hB.add hc using 1
  funext w
  unfold actualParisiFullScalarProcess
  rfl

theorem support_value_memLp_two (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    MemLp (fun w => parisiPhysicalValue β (parisiEquilibriumMeasure β)
      (parisiEquilibriumPhysicalEndpoint β)
      (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) w)) 2 W.law := by
  let := W.isProbability
  let f : ℝ → ℝ := fun y => softAbs 1 y - softAbs 1 0
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [f, Real.dist_eq, sub_sub_sub_cancel_right] using
      (softAbs_lipschitz (by norm_num : (1 : ℝ) ≠ 0)).dist_le_mul y z
  have hcomp := hf.comp_memLp (by dsimp [f]; ring)
    (fullScalar_memLp_two W β (parisiEquilibriumPhysicalEndpoint β))
  have hh := (hcomp.add (memLp_const (softAbs 1 0))).add
    (memLp_const ((β ^ 2 - (parisiEquilibriumPhysicalEndpoint β : ℝ)) / 2))
  convert! hh using 1
  funext w
  rw [LJ.support_potential_value β hβ]
  simp only [Function.comp_def, Pi.add_apply, f, softAbs, one_mul, div_one, sub_add_cancel]

theorem measurable_supportFieldTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Measurable (supportFieldTarget (A := A) W β hβ) := by
  have hy : Measurable (fun u : (Bool × Ω) × A =>
      actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) u.1.2) := by
    unfold actualParisiFullScalarProcess
    exact ((actualParisiFullScalarDrift β).solution_measurable W
      (parisiEquilibriumPhysicalEndpoint β)).comp (measurable_snd.comp measurable_fst)
  have hx : Measurable (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)
  have hval : Measurable (parisiPhysicalValue β (parisiEquilibriumMeasure β)
      (parisiEquilibriumPhysicalEndpoint β)) := by
    have he : parisiPhysicalValue β (parisiEquilibriumMeasure β)
        (parisiEquilibriumPhysicalEndpoint β) = fun y =>
        Real.log (2 * Real.cosh y) + (β ^ 2 - (parisiEquilibriumPhysicalEndpoint β : ℝ)) / 2 :=
      funext (LJ.support_potential_value β hβ)
    rw [he]
    exact ((Real.measurable_log.comp (measurable_const.mul Real.continuous_cosh.measurable))).add_const _
  convert! (((((LJ.measurable_actualRowPotential W β _).comp measurable_fst).const_mul
    (β ^ 2 * actualParisiFullSusceptibilityExpected W β (parisiEquilibriumPhysicalEndpoint β))).add
    (hx.mul hy)).sub (hval.comp hy)).add_const
      (parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0) |>.sub
      (((SJ3.measurable_potentialIntegral W β hβ (parisiEquilibriumPhysicalEndpoint β)).comp
        measurable_fst).const_mul (β ^ 2)) using 1

theorem supportFieldTarget_memLp_two (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) : MemLp (supportFieldTarget W β hβ) 2 (LM4.actualRowBaseLaw W Z) := by
  let := W.isProbability
  let := Z.isProbability
  have hA : MemLp (fun u : (Bool × Ω) × A =>
      LJ.actualRowPotential W β (parisiEquilibriumPhysicalEndpoint β) u.1) 2
      (LM4.actualRowBaseLaw W Z) :=
    MemLp.of_bound ((LJ.measurable_actualRowPotential W β _).comp measurable_fst).aestronglyMeasurable 2
      (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using
        SJ3.actualRowPotential_bound W β _ u.1))
  have hy : MemLp (fun u : (Bool × Ω) × A =>
      actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) u.1.2) 2
      (LM4.actualRowBaseLaw W Z) :=
    ((fullScalar_memLp_two W β _).comp_snd (scalarHiddenPriorBool 0)).comp_fst Z.law
  have hxy : MemLp (fun u : (Bool × Ω) × A =>
      scalarHiddenSign u.1.1 * actualParisiFullScalarProcess W β
        (parisiEquilibriumPhysicalEndpoint β) u.1.2) 2 (LM4.actualRowBaseLaw W Z) := by
    apply hy.congr_norm
      ((((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable).mul
        hy.aestronglyMeasurable)
    apply ae_of_all
    intro u
    simp only [Real.norm_eq_abs]
    cases h : u.1.1 <;> simp [scalarHiddenSign, h]
  have hU : MemLp (fun u : (Bool × Ω) × A =>
      parisiPhysicalValue β (parisiEquilibriumMeasure β) (parisiEquilibriumPhysicalEndpoint β)
        (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) u.1.2)) 2
      (LM4.actualRowBaseLaw W Z) :=
    ((support_value_memLp_two W β hβ).comp_snd (scalarHiddenPriorBool 0)).comp_fst Z.law
  have hP : MemLp (fun u : (Bool × Ω) × A =>
      SJ3.potentialIntegral W β hβ (parisiEquilibriumPhysicalEndpoint β) u.1) 2
      (LM4.actualRowBaseLaw W Z) :=
    (SJ3.potentialIntegral_memLp W β hβ _).comp_fst Z.law
  convert! (((hA.const_mul (β ^ 2 * actualParisiFullSusceptibilityExpected W β
      (parisiEquilibriumPhysicalEndpoint β))).add hxy).sub hU |>.add
      (memLp_const (parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0))).sub
    (hP.const_mul (β ^ 2)) using 1

theorem measurable_supportFieldLeftSum (W : BrownianSystem Ω) (β : ℝ) (l : ℕ) :
    Measurable (supportFieldLeftSum (A := A) W β l) := by
  apply Finset.measurable_sum
  intro k _
  exact (((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
    ((measurable_actualParisiFullPosteriorMean W β _).comp
      (measurable_snd.comp measurable_fst))).mul
    (((W.measurable _).sub (W.measurable _)).comp (measurable_snd.comp measurable_fst))

theorem supportFieldLeftSum_memLp_two (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (l : ℕ) : MemLp (supportFieldLeftSum W β l) 2 (LM4.actualRowBaseLaw W Z) := by
  let := W.isProbability
  let := Z.isProbability
  unfold supportFieldLeftSum
  apply memLp_finsetSum
  intro k _
  let t := (brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l
  have hΔ : MemLp (fun u : (Bool × Ω) × A =>
      W.B (t (k + 1)) u.1.2 - W.B (t k) u.1.2) 2 (LM4.actualRowBaseLaw W Z) :=
    (((W.brownian.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.sub
      (W.brownian.isGaussianProcess.hasGaussianLaw_eval _).memLp_two).comp_snd
        (scalarHiddenPriorBool 0)).comp_fst Z.law
  have hcoeff : Measurable (fun u : (Bool × Ω) × A =>
      scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t k) u.1.2) :=
    ((measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_fst)).sub
      ((measurable_actualParisiFullPosteriorMean W β _).comp (measurable_snd.comp measurable_fst))
  apply hΔ.of_le_mul (c := 2) (hcoeff.aestronglyMeasurable.mul hΔ.aestronglyMeasurable)
  apply ae_of_all
  intro u
  change |(scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t k) u.1.2) *
    (W.B (t (k + 1)) u.1.2 - W.B (t k) u.1.2)| ≤
    2 * |W.B (t (k + 1)) u.1.2 - W.B (t k) u.1.2|
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hm : |actualParisiFullPosteriorMean W β (t k) u.1.2| ≤ 1 := by
    simpa only [actualParisiFullPosteriorMean, actualParisiMagnetizationObservable] using
      actualParisiMagnetizationObservable_abs_le W β (t k) u.1.2
  have hx : |scalarHiddenSign u.1.1| = 1 := by
    cases h : u.1.1 <;> norm_num [scalarHiddenSign, h]
  exact (abs_sub _ _).trans (by rw [hx]; linarith)

theorem supportField_squared_errors_integrable (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (l : ℕ) :
    Integrable (fun u => (supportFieldLeftSum W β l u - supportFieldTarget W β hβ u) ^ 2)
      (LM4.actualRowBaseLaw W Z) :=
  ((supportFieldLeftSum_memLp_two W Z β l).sub
    (supportFieldTarget_memLp_two W Z β hβ)).integrable_sq

def supportItoLeftSum (W : BrownianSystem Ω) (β : ℝ) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    actualParisiFullPosteriorMean W β
      ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) w *
    (W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l (k + 1)) w -
      W.B ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) w)

omit [MeasurableSpace A] in
theorem supportFieldLeftSum_eq (W : BrownianSystem Ω) (β : ℝ) (l : ℕ)
    (u : (Bool × Ω) × A) :
    supportFieldLeftSum W β l u = scalarHiddenSign u.1.1 *
      (W.B (parisiEquilibriumPhysicalEndpoint β) u.1.2 - W.B 0 u.1.2) -
      supportItoLeftSum W β l u.1.2 := by
  unfold supportFieldLeftSum supportItoLeftSum
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_range_sub (fun k => W.B
      ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) u.1.2)]
  rw [(brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).zero]
  simp [brownianDyadicGrid]

theorem supportField_squared_error_eq (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (l : ℕ) :
    (fun u => (supportFieldLeftSum W β l u - supportFieldTarget W β hβ u) ^ 2)
      =ᵐ[LM4.actualRowBaseLaw W Z]
    (fun u => (supportItoLeftSum W β l u.1.2 - supportItoPrimitive W β u.1.2) ^ 2) := by
  let := W.isProbability
  let := Z.isProbability
  have hz := (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
    (ν := Z.law)).quasiMeasurePreserving.ae
    ((measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).quasiMeasurePreserving.ae
      W.brownian.eval_zero_ae_eq_zero)
  filter_upwards [supportFieldTarget_eq_itoPrimitive W Z β hβ, hz] with u hu hu0
  rw [supportFieldLeftSum_eq, hu, hu0, sub_zero]
  ring

theorem supportField_meanSquare_eq (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (l : ℕ) :
    (∫ u, (supportFieldLeftSum W β l u - supportFieldTarget W β hβ u) ^ 2
      ∂LM4.actualRowBaseLaw W Z) =
    ∫ w, (supportItoLeftSum W β l w - supportItoPrimitive W β w) ^ 2 ∂W.law := by
  let := W.isProbability
  let := Z.isProbability
  rw [integral_congr_ae (supportField_squared_error_eq W Z β hβ l)]
  calc
    _ = ∫ u : Bool × Ω, (supportItoLeftSum W β l u.2 - supportItoPrimitive W β u.2) ^ 2
        ∂(scalarHiddenPriorBool 0).prod W.law := by
      simpa only [LM4.actualRowBaseLaw, probReal_univ, one_smul] using
        integral_fun_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law)
          (fun u => (supportItoLeftSum W β l u.2 - supportItoPrimitive W β u.2) ^ 2)
    _ = _ := by
      simpa only [probReal_univ, one_smul] using
        integral_fun_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)
          (fun w => (supportItoLeftSum W β l w - supportItoPrimitive W β w) ^ 2)

theorem physicalTime_pre_mem (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) :
    (t : ℝ) / β ^ 2 ∈ Ico (0 : ℝ) 1 := by
  have hb := sq_pos_of_pos (zero_lt_one.trans hβ)
  have ht' := NNReal.coe_le_coe.mpr ht
  rw [parisiEquilibriumPhysicalEndpoint_coe β hβ] at ht'
  exact ⟨div_nonneg t.coe_nonneg hb.le,
    ((div_le_iff₀ hb).mpr (by simpa only [mul_comm] using ht')).trans_lt
      (parisiEquilibriumSupportEndpoint_spec β hβ).1.2⟩

theorem physicalValue_hasDerivAt_pre (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (y : ℝ) :
    HasDerivAt (parisiPhysicalValue β (parisiEquilibriumMeasure β) t)
      (actualParisiFullMagnetization β t y) y := by
  have hq := physicalTime_pre_mem β hβ t ht
  have hrem : Real.toNNReal (1 - (t : ℝ) / β ^ 2) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hq.1]
  unfold parisiPhysicalValue
  rw [parisiCDFValue_eq_upstream]
  simpa only [actualParisiFullMagnetization, cdfTimeClamp_eq ⟨hq.1, hq.2.le⟩] using
    scalarCDFValue_hasDerivAt β (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
      (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono _ _ hrem y

theorem physicalValue_contDiff_pre (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) :
    ContDiff ℝ ∞ (parisiPhysicalValue β (parisiEquilibriumMeasure β) t) := by
  have hq := physicalTime_pre_mem β hβ t ht
  unfold parisiPhysicalValue
  rw [parisiCDFValue_eq_upstream]
  exact (scalarCDFValue_regularDatum β (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) (zero_lt_one.trans hβ).ne' hq.1 hq.2).smooth

theorem physicalValue_third_derivative_bound_pre (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (y : ℝ) :
    |iteratedDeriv 3 (parisiPhysicalValue β (parisiEquilibriumMeasure β) t) y| ≤
      (susceptibilityLipschitzConstant : ℝ) := by
  have hd : deriv (parisiPhysicalValue β (parisiEquilibriumMeasure β) t) =
      actualParisiFullMagnetization β t :=
    funext (fun y => (physicalValue_hasDerivAt_pre β hβ t ht y).deriv)
  have hdd : deriv (deriv (parisiPhysicalValue β (parisiEquilibriumMeasure β) t)) =
      actualParisiFullCurvature β t := by
    rw [hd]
    exact funext (fun y => (actualParisiFullMagnetization_hasDerivAt β t y).deriv)
  have he : iteratedDeriv 3 (parisiPhysicalValue β (parisiEquilibriumMeasure β) t) y =
      deriv (actualParisiFullCurvature β t) y := by
    rw [iteratedDeriv_eq_iterate]
    change deriv (deriv (deriv (parisiPhysicalValue β (parisiEquilibriumMeasure β) t))) y = _
    rw [hdd]
  rw [he]
  exact norm_deriv_le_of_lipschitz (actualParisiFullCurvature_lipschitz β t)

theorem physicalValue_taylorWithinEval_two_pre (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (z y : ℝ) (hzy : z ≠ y) :
    taylorWithinEval (parisiPhysicalValue β (parisiEquilibriumMeasure β) t) 2 (uIcc z y) z y =
      parisiPhysicalValue β (parisiEquilibriumMeasure β) t z +
        actualParisiFullMagnetization β t z * (y - z) +
        actualParisiFullCurvature β t z * (y - z) ^ 2 / 2 := by
  let f := parisiPhysicalValue β (parisiEquilibriumMeasure β) t
  have hs := physicalValue_contDiff_pre β hβ t ht
  have hw (k : ℕ) : iteratedDerivWithin k f (uIcc z y) z = iteratedDeriv k f z :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hzy)
      (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).contDiffAt left_mem_uIcc
  have hd : deriv f = actualParisiFullMagnetization β t :=
    funext (fun x => (physicalValue_hasDerivAt_pre β hβ t ht x).deriv)
  have hdd : deriv (deriv f) = actualParisiFullCurvature β t := by
    rw [hd]
    exact funext (fun x => (actualParisiFullMagnetization_hasDerivAt β t x).deriv)
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hw 0, hw 1, hw 2]
  norm_num [iteratedDeriv_eq_iterate, hd, f,
    (actualParisiFullMagnetization_hasDerivAt β t z).deriv]
  ring

theorem physicalValue_taylor_two_abs_le_pre (β : ℝ) (hβ : 1 < β) (t : ℝ≥0)
    (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (z y : ℝ) :
    |parisiPhysicalValue β (parisiEquilibriumMeasure β) t y -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) t z -
      actualParisiFullMagnetization β t z * (y - z) -
      actualParisiFullCurvature β t z * (y - z) ^ 2 / 2| ≤
        (susceptibilityLipschitzConstant : ℝ) * |y - z| ^ 3 / 6 := by
  by_cases hzy : z = y
  · subst y
    simp
  obtain ⟨u, _, hu⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := parisiPhysicalValue β (parisiEquilibriumMeasure β) t) (n := 2) hzy
    ((physicalValue_contDiff_pre β hβ t ht).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffOn
  rw [physicalValue_taylorWithinEval_two_pre β hβ t ht z y hzy] at hu
  have he : parisiPhysicalValue β (parisiEquilibriumMeasure β) t y -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) t z -
      actualParisiFullMagnetization β t z * (y - z) -
      actualParisiFullCurvature β t z * (y - z) ^ 2 / 2 =
      iteratedDeriv 3 (parisiPhysicalValue β (parisiEquilibriumMeasure β) t) u * (y - z) ^ 3 / 6 := by
    norm_num at hu
    linarith
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (physicalValue_third_derivative_bound_pre β hβ t ht u)
      (pow_nonneg (abs_nonneg _) 3)) (by norm_num)

theorem physicalValue_time_increment_pre (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0)
    (hst : s ≤ t) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (y : ℝ) :
    parisiPhysicalValue β (parisiEquilibriumMeasure β) t y -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) s y =
      ∫ r in (s : ℝ)..(t : ℝ), -(1 / 2 : ℝ) *
        (actualParisiFullCurvature β r y +
          cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) *
            (actualParisiFullMagnetization β r y) ^ 2) := by
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have hq := physicalTime_pre_mem β hβ t ht
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ)
  have ha : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩
  have h1 : α 1 = 1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have H := scalarCDFValue_integral_time_equation β α ha h1 hb
    (div_nonneg s.coe_nonneg (sq_nonneg β))
    (div_le_div_of_nonneg_right (NNReal.coe_le_coe.mpr hst) (sq_nonneg β)) hq.2 y
  unfold parisiPhysicalValue
  rw [parisiCDFValue_eq_upstream, parisiCDFValue_eq_upstream]
  calc
    _ = ∫ q in (s : ℝ) / β ^ 2..(t : ℝ) / β ^ 2, scalarCDFValueRate β α q y := H
    _ = ∫ r in (s : ℝ)..(t : ℝ), (1 / β ^ 2) * scalarCDFValueRate β α (r / β ^ 2) y := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_div (fun q => scalarCDFValueRate β α q y) (pow_ne_zero 2 hb),
        smul_eq_mul]
      field_simp
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le (NNReal.coe_le_coe.mpr hst)] at hr
      have hrq : r / β ^ 2 ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (s.coe_nonneg.trans hr.1) (sq_nonneg β),
          (div_le_div_of_nonneg_right hr.2 (sq_nonneg β)).trans hq.2.le⟩
      dsimp only
      simp only [scalarCDFValueRate, actualParisiFullCurvature, actualParisiFullMagnetization,
        cdfTimeClamp_eq hrq]
      dsimp only [α]
      field_simp

theorem physicalValue_time_space_remainder_pre (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0)
    (hst : s ≤ t) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (z y : ℝ) :
    |parisiPhysicalValue β (parisiEquilibriumMeasure β) t y -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) s z -
      actualParisiFullMagnetization β s z * (y - z) -
      actualParisiFullCurvature β s z * (y - z) ^ 2 / 2 +
      (1 / 2 : ℝ) * ∫ r in (s : ℝ)..(t : ℝ),
        actualParisiFullCurvature β r y +
          cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) *
            (actualParisiFullMagnetization β r y) ^ 2| ≤
      (susceptibilityLipschitzConstant : ℝ) * |y - z| ^ 3 / 6 := by
  have H := physicalValue_time_increment_pre β hβ s t hst ht y
  rw [intervalIntegral.integral_const_mul] at H
  have he : parisiPhysicalValue β (parisiEquilibriumMeasure β) t y -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) s z -
      actualParisiFullMagnetization β s z * (y - z) -
      actualParisiFullCurvature β s z * (y - z) ^ 2 / 2 +
      (1 / 2 : ℝ) * (∫ r in (s : ℝ)..(t : ℝ),
        actualParisiFullCurvature β r y +
          cdf (parisiEquilibriumMeasure β : Measure ℝ) (r / β ^ 2) *
            (actualParisiFullMagnetization β r y) ^ 2) =
      parisiPhysicalValue β (parisiEquilibriumMeasure β) s y -
        parisiPhysicalValue β (parisiEquilibriumMeasure β) s z -
        actualParisiFullMagnetization β s z * (y - z) -
        actualParisiFullCurvature β s z * (y - z) ^ 2 / 2 := by
    linear_combination H
  rw [he]
  exact physicalValue_taylor_two_abs_le_pre β hβ s (hst.trans ht) z y

end SKConstants.Completion.S32bA
