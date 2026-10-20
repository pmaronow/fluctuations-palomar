module

public import SKConstants.Completion.LC1.StieltjesPrimitive
public import SKConstants.BrownianPathNormCaps
public import SKConstants.ScalarOrthogonalWeightedBrownian

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_primitiveBrownianPath_norm (W : BrownianSystem Ω) (H : ℝ≥0) :
    Integrable (fun w => ‖scalarPrimitiveBrownianPathVersion W H w‖) W.law := by
  let := W.isProbability
  obtain ⟨a,ha,he⟩ := BrownianNormCaps.primitivePathLaw_fernique W H
  have hn : Integrable (fun p : ScalarContinuousPath H => ‖p‖) (scalarPrimitiveBrownianPathLaw W H) := by
    apply ((integrable_const (1:ℝ)).add (he.const_mul a⁻¹)).mono' continuous_norm.measurable.aestronglyMeasurable
    apply ae_of_all
    intro p
    rw [norm_norm]
    have hx : ‖p‖ ≤ 1+‖p‖^2 := by nlinarith [sq_nonneg (‖p‖-1)]
    have hsq : a * ‖p‖^2 ≤ Real.exp (a*‖p‖^2) := by
      linarith [Real.add_one_le_exp (a*‖p‖^2)]
    have hinv := mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr ha.le)
    rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at hinv
    change ‖p‖ ≤ 1 + a⁻¹ * Real.exp (a*‖p‖^2)
    linarith
  have hl : HasLaw (scalarPrimitiveBrownianPathVersion W H) (scalarPrimitiveBrownianPathLaw W H) W.law :=
    ⟨(measurable_scalarPrimitiveBrownianPathVersion W H).aemeasurable,rfl⟩
  exact hl.integrable_comp hn

attribute [local irreducible] BrownianSystem.driver BrownianSystem.progressiveVersion

lemma measurable_brownianDriver_real (W : BrownianSystem Ω) :
    Measurable (fun q : ℝ × Ω => W.driver q.1.toNNReal q.2) := by
  have hm : Measurable (fun q : ℝ≥0 × Ω => W.driver q.1 q.2) :=
    progressive_joint_measurable _ W.driver_progressive
  exact hm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

theorem brownianDriver_bounded_time_prod_integrable
    (W : BrownianSystem Ω) (μ : Measure ℝ) [IsFiniteMeasure μ] (H : ℝ≥0)
    (hμ : ∀ᵐ r ∂μ, r ∈ Icc (0:ℝ) (H:ℝ)) :
    Integrable (fun q : ℝ × Ω => W.driver q.1.toNNReal q.2) (μ.prod W.law) := by
  let := W.isProbability
  have hpath : ∀ᵐ w ∂W.law, ∀ r ∈ Icc (0:ℝ) (H:ℝ),
      |W.driver r.toNNReal w| ≤ ‖scalarPrimitiveBrownianPathVersion W H w‖ := by
    filter_upwards [scalarPrimitiveBrownianPathVersion_ae W H,W.driver_indistinguishable] with w hp hd
    intro r hr
    have hrN : (⟨r,hr.1⟩:ℝ≥0) = r.toNNReal := NNReal.coe_injective (Real.coe_toNNReal _ hr.1).symm
    have hv : W.driver r.toNNReal w = scalarPrimitiveBrownianPathVersion W H w ⟨r,hr⟩ := by
      rw [hd,hp,hrN]
    rw [hv]
    simpa only [Real.norm_eq_abs] using (scalarPrimitiveBrownianPathVersion W H w).norm_coe_le_norm ⟨r,hr⟩
  have hm := measurable_brownianDriver_real W
  have hn : Measurable (fun q : ℝ × Ω => ‖scalarPrimitiveBrownianPathVersion W H q.2‖) :=
    ((measurable_scalarPrimitiveBrownianPathVersion W H).norm).comp measurable_snd
  apply ((integrable_primitiveBrownianPath_norm W H).comp_snd μ).mono' hm.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm hn)).mpr
  filter_upwards [hμ] with r hr
  filter_upwards [hpath] with w hw
  simpa only [Real.norm_eq_abs] using hw r hr

lemma integrable_brownianDriver_eval (W : BrownianSystem Ω) (S : ℝ≥0) :
    Integrable (W.driver S) W.law :=
  (W.brownian.integrable_eval S).congr (W.driver_indistinguishable.mono (fun _ hw => (hw S).symm))

theorem bounded_brownian_increment_time_prod_integrable
    (W : BrownianSystem Ω) (μ : Measure ℝ) [IsFiniteMeasure μ] (H S : ℝ≥0)
    (hμ : ∀ᵐ r ∂μ, r ∈ Icc (0:ℝ) (H:ℝ))
    (F : Ω → ℝ) (hF : Measurable F) (C : ℝ≥0) (hFC : ∀ w, |F w| ≤ C) :
    Integrable (fun q : ℝ × Ω => F q.2 * (W.driver q.1.toNNReal q.2-W.driver S q.2)) (μ.prod W.law) := by
  let := W.isProbability
  apply ((brownianDriver_bounded_time_prod_integrable W μ H hμ).sub
    ((integrable_brownianDriver_eval W S).comp_snd μ)).bdd_mul
    (hF.comp measurable_snd).aestronglyMeasurable
  exact ae_of_all _ (fun q => by rw [Real.norm_eq_abs]; exact hFC q.2)

theorem brownianStieltjes_increment_version (W : BrownianSystem Ω)
    (f : StieltjesFunction ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    (fun w => scalarGlobalStieltjesWeightedProcess f W.driver T w -
      scalarGlobalStieltjesWeightedProcess f W.driver S w) =ᵐ[W.law]
    (fun w => f T * (W.driver T w-W.driver S w) -
      ∫ r in (S:ℝ)..(T:ℝ), W.driver r.toNNReal w-W.driver S w ∂f.measure) := by
  filter_upwards [W.driver_continuous] with w hw
  have hc : Continuous (fun r : ℝ => W.driver r.toNNReal w) := hw.comp continuous_real_toNNReal
  have hi (a b : ℝ) : IntervalIntegrable (fun r => W.driver r.toNNReal w) f.measure a b :=
    (hc.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
  have he := intervalIntegral.integral_add_adjacent_intervals (hi 0 S) (hi S T)
  unfold scalarGlobalStieltjesWeightedProcess
  rw [intervalIntegral.integral_sub (hi S T) intervalIntegrable_const,
    scalarStieltjes_integral_const f (NNReal.coe_le_coe.mpr hST) (W.driver S w)]
  rw [← he]
  ring

theorem bounded_brownian_stieltjes_expectation_swap
    (W : BrownianSystem Ω) (f : StieltjesFunction ℝ) (S T : ℝ≥0) (hST : S ≤ T)
    (F : Ω → ℝ) (hF : Measurable F) (C : ℝ≥0) (hFC : ∀ w, |F w| ≤ C) :
    (∫ w, F w * (∫ r in (S:ℝ)..(T:ℝ), W.driver r.toNNReal w-W.driver S w ∂f.measure) ∂W.law) =
    ∫ r in (S:ℝ)..(T:ℝ), (∫ w, F w * (W.driver r.toNNReal w-W.driver S w) ∂W.law) ∂f.measure := by
  let := W.isProbability
  let μ := f.measure.restrict (Ioc (S:ℝ) (T:ℝ))
  let _ : IsFiniteMeasure μ := ⟨by
    change (f.measure.restrict (Ioc (S:ℝ) (T:ℝ))) univ < ⊤
    rw [Measure.restrict_apply_univ,f.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  have hμ : ∀ᵐ r ∂μ, r ∈ Icc (0:ℝ) (T:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨S.coe_nonneg.trans hr.1.le,hr.2⟩
  have hi := bounded_brownian_increment_time_prod_integrable W μ T S hμ F hF C hFC
  simp only [intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hST)]
  simp_rw [← integral_const_mul]
  exact (integral_integral_swap (μ:=μ) (ν:=W.law)
    (f:=fun r w => F w * (W.driver r.toNNReal w-W.driver S w)) hi).symm

theorem bounded_brownian_stieltjes_integrable
    (W : BrownianSystem Ω) (f : StieltjesFunction ℝ) (S T : ℝ≥0) (hST : S ≤ T)
    (F : Ω → ℝ) (hF : Measurable F) (C : ℝ≥0) (hFC : ∀ w, |F w| ≤ C) :
    Integrable (fun w => F w * (∫ r in (S:ℝ)..(T:ℝ),
      W.driver r.toNNReal w-W.driver S w ∂f.measure)) W.law ∧
    Integrable (fun w => F w * (scalarGlobalStieltjesWeightedProcess f W.driver T w -
      scalarGlobalStieltjesWeightedProcess f W.driver S w)) W.law := by
  let := W.isProbability
  let μ := f.measure.restrict (Ioc (S:ℝ) (T:ℝ))
  let _ : IsFiniteMeasure μ := ⟨by
    change (f.measure.restrict (Ioc (S:ℝ) (T:ℝ))) univ < ⊤
    rw [Measure.restrict_apply_univ,f.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  have hμ : ∀ᵐ r ∂μ, r ∈ Icc (0:ℝ) (T:ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact ⟨S.coe_nonneg.trans hr.1.le,hr.2⟩
  have hi := (bounded_brownian_increment_time_prod_integrable W μ T S hμ F hF C hFC).integral_prod_right
  have hiTime : Integrable (fun w => F w * (∫ r in (S:ℝ)..(T:ℝ),
      W.driver r.toNNReal w-W.driver S w ∂f.measure)) W.law := by
    simpa only [intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hST), integral_const_mul] using hi
  refine ⟨hiTime,?_⟩
  have hiEnd := (((integrable_brownianDriver_eval W T).sub (integrable_brownianDriver_eval W S)).bdd_mul
    hF.aestronglyMeasurable (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hFC w))).const_mul (f T)
  apply (hiEnd.sub hiTime).congr
  filter_upwards [brownianStieltjes_increment_version W f S T hST] with w hw
  change f T * (F w * (W.driver T w-W.driver S w)) -
    F w * (∫ r in (S:ℝ)..(T:ℝ), W.driver r.toNNReal w-W.driver S w ∂f.measure) = _
  rw [hw]
  ring

theorem bounded_brownian_stieltjes_increment_integral
    (W : BrownianSystem Ω) (f : StieltjesFunction ℝ) (S T : ℝ≥0) (hST : S ≤ T)
    (F : Ω → ℝ) (hF : Measurable F) (C : ℝ≥0) (hFC : ∀ w, |F w| ≤ C) :
    (∫ w, F w * (scalarGlobalStieltjesWeightedProcess f W.driver T w -
      scalarGlobalStieltjesWeightedProcess f W.driver S w) ∂W.law) =
      f T * (∫ w, F w * (W.driver T w-W.driver S w) ∂W.law) -
      (∫ r in (S:ℝ)..(T:ℝ), (∫ w, F w * (W.driver r.toNNReal w-W.driver S w) ∂W.law) ∂f.measure) := by
  have hiTime := (bounded_brownian_stieltjes_integrable W f S T hST F hF C hFC).1
  have hiEnd := (((integrable_brownianDriver_eval W T).sub (integrable_brownianDriver_eval W S)).bdd_mul
    hF.aestronglyMeasurable (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hFC w))).const_mul (f T)
  calc
    _ = ∫ w, f T * (F w * (W.driver T w-W.driver S w)) -
        F w * (∫ r in (S:ℝ)..(T:ℝ), W.driver r.toNNReal w-W.driver S w ∂f.measure) ∂W.law := by
      apply integral_congr_ae
      filter_upwards [brownianStieltjes_increment_version W f S T hST] with w hw
      rw [hw]
      ring
    _ = _ := by
      rw [integral_sub
        (f:=fun w => f T * (F w * (W.driver T w-W.driver S w)))
        (g:=fun w => F w * (∫ r in (S:ℝ)..(T:ℝ), W.driver r.toNNReal w-W.driver S w ∂f.measure))
        hiEnd hiTime, integral_const_mul,
        bounded_brownian_stieltjes_expectation_swap W f S T hST F hF C hFC]

lemma integral_brownianDriver_eq_zero (W : BrownianSystem Ω) (t : ℝ≥0) :
    (∫ w, W.driver t w ∂W.law) = 0 :=
  (integral_congr_ae (W.driver_indistinguishable.mono (fun _ hw => hw t))).trans
    (W.brownian.integral_eval t)

theorem brownianStieltjes_increment_mean_zero (W : BrownianSystem Ω)
    (f : StieltjesFunction ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ w, scalarGlobalStieltjesWeightedProcess f W.driver T w -
      scalarGlobalStieltjesWeightedProcess f W.driver S w ∂W.law) = 0 := by
  have hh := bounded_brownian_stieltjes_increment_integral W f S T hST (fun _ => (1:ℝ))
    measurable_const 1 (fun _ => by norm_num)
  simp only [one_mul] at hh
  have hz (r : ℝ≥0) : (∫ w, W.driver r w-W.driver S w ∂W.law) = 0 := by
    rw [integral_sub (integrable_brownianDriver_eval W r) (integrable_brownianDriver_eval W S),
      integral_brownianDriver_eq_zero,integral_brownianDriver_eq_zero,sub_self]
  simpa only [hz,mul_zero,intervalIntegral.integral_zero,sub_zero] using hh

end SKConstants.Completion.LC1
