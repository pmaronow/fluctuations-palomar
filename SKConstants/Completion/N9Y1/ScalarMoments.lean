module

public import SKConstants.Completion.N9Y1.GaussianMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N9Y1
open SKConstantsOAI.ZeroTemperatureSK LBase NScalar LFine N9b
variable {Ω : Type*} [MeasurableSpace Ω]

theorem brownianStaticPredictableSum_moments_le_of_coefficient_budget
    {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q) (hmB : ∀ t, Measurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (hcap : ∀ k u, |H k u| ≤ 1)
    (b : ℝ) (hbudget : ∀ k, (∫ u, brownianStaticCoefficient B t H k u^2 ∂P.prod Q) ≤ b)
    (n : ℕ) :
    Integrable (fun u => brownianStaticPredictableSum B t H n u^2) (P.prod Q) ∧
      Integrable (fun u => brownianStaticPredictableSum B t H n u^4) (P.prod Q) ∧
      (∫ u, brownianStaticPredictableSum B t H n u^2 ∂P.prod Q) ≤ ((t n : ℝ)-t 0)*b ∧
      (∫ u, brownianStaticPredictableSum B t H n u^4 ∂P.prod Q) ≤ 3*((t n : ℝ)-t 0)^2*b := by
  have hsnd : HasLaw (Prod.snd : A × Ω → Ω) Q (P.prod Q) :=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  have hm := predictableGaussianSum_moments_le_of_coefficient_budget (P.prod Q)
    (fun k u => brownianMeshIncrement B t k u.2) (brownianStaticCoefficient B t H)
    (brownianMeshVariance t) (fun k => (brownianMeshIncrement_hasLaw hB t ht k).comp hsnd)
    (aemeasurable_brownianStaticCoefficient P Q B hB hmB t H hH)
    (fun k => ae_of_all _ fun u => hcap k (u.1,brownianFullPast B (t k) u.2))
    (brownianStaticPredictable_state_indep_increment P Q B hB hmB t ht H hH) b hbudget n
  have hsum : (∑ k ∈ Finset.range n, (brownianMeshVariance t k : ℝ)) = (t n : ℝ)-t 0 := by
    simp only [brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ _))]
    exact Finset.sum_range_sub (fun k => (t k : ℝ)) n
  simpa only [hsum,brownianStaticPredictableSum] using hm

theorem actualCurvatureDyadicIntervalSum_past_weighted_moments_le
    (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (hst : s ≤ t)
    (F : (Iic s → ℝ) → ℝ) (hF : Measurable F) (hFcap : ∀ p, |F p| ≤ 1)
    (l : ℕ) :
    (∫ w, (F (brownianFullPast W.B s w)*actualCurvatureDyadicIntervalSum W β s t l w)^2 ∂W.law) ≤
        ((t : ℝ)-s)*(∫ w, F (brownianFullPast W.B s w)^2 ∂W.law) ∧
      (∫ w, (F (brownianFullPast W.B s w)*actualCurvatureDyadicIntervalSum W β s t l w)^4 ∂W.law) ≤
        3*((t : ℝ)-s)^2*(∫ w, F (brownianFullPast W.B s w)^2 ∂W.law) := by
  let := W.isProbability
  let T : ℕ → ℝ≥0 := fun k => s+(t-s)*((k : ℝ≥0)/2^l)
  have hT : Monotone T := by intro i j hij; dsimp [T]; gcongr
  have hsT (k : ℕ) : s ≤ T k := le_add_of_nonneg_right (by positivity)
  let H : BrownianStaticPredictableCoefficient Unit T := fun k u =>
    F (brownianPastRestrict (hsT k) u.2)*curvaturePastCoefficient β (T k) u
  have hHm (k) : Measurable (H k) :=
    (hF.comp ((measurable_brownianPastRestrict _).comp measurable_snd)).mul
      (measurable_curvaturePastCoefficient β (T k))
  have hcap (k) (u : Unit × (Iic (T k) → ℝ)) : |H k u| ≤ 1 := by
    change |F _*curvaturePastCoefficient β (T k) u| ≤ 1
    rw [abs_mul]
    exact (mul_le_mul (hFcap _) (curvaturePastCoefficient_norm_le β (T k) u)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hFm : Measurable (fun w => F (brownianFullPast W.B s w)) :=
    hF.comp (Measurable.of_eval (fun u : Iic s => W.measurable u))
  have hF2 : Integrable (fun w => F (brownianFullPast W.B s w)^2) W.law :=
    (MemLp.of_bound hFm.aestronglyMeasurable 1
      (ae_of_all _ fun w => by simpa only [Real.norm_eq_abs] using hFcap _)
      : MemLp (fun w => F (brownianFullPast W.B s w)) 2 W.law).integrable_sq
  have hbudget (k) :
      (∫ u, brownianStaticCoefficient W.B T H k u^2 ∂(Measure.dirac ()).prod W.law) ≤
        ∫ w, F (brownianFullPast W.B s w)^2 ∂W.law := by
    rw [integral_unit_prod]
    have hCm : Measurable (fun w => brownianStaticCoefficient W.B T H k ((),w)) :=
      (hHm k).comp (measurable_const.prodMk
        (Measurable.of_eval (fun u : Iic (T k) => W.measurable u)))
    have hi : Integrable (fun w => brownianStaticCoefficient W.B T H k ((),w)^2) W.law :=
      Integrable.of_bound (hCm.pow_const 2).aestronglyMeasurable 1
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
          have hh := hcap k ((),brownianFullPast W.B (T k) w)
          change |brownianStaticCoefficient W.B T H k ((),w)| ≤ 1 at hh
          nlinarith [sq_abs (brownianStaticCoefficient W.B T H k ((),w)),
            abs_nonneg (brownianStaticCoefficient W.B T H k ((),w))])
    apply integral_mono_ae hi hF2
    apply ae_of_all
    intro w
    change (F (brownianFullPast W.B s w)*curvaturePastCoefficient β (T k)
      ((),brownianFullPast W.B (T k) w))^2 ≤ _
    have hh := curvaturePastCoefficient_norm_le β (T k) ((),brownianFullPast W.B (T k) w)
    rw [Real.norm_eq_abs] at hh
    have hsquare : (curvaturePastCoefficient β (T k) ((),brownianFullPast W.B (T k) w))^2 ≤ 1 := by
      nlinarith [sq_abs (curvaturePastCoefficient β (T k) ((),brownianFullPast W.B (T k) w)),
        abs_nonneg (curvaturePastCoefficient β (T k) ((),brownianFullPast W.B (T k) w))]
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)).trans_eq (mul_one _)
  have hm := brownianStaticPredictableSum_moments_le_of_coefficient_budget
    (Measure.dirac ()) W.law W.B W.brownian.toIsPreBrownianReal W.measurable
    T hT H hHm hcap _ hbudget (2^l)
  have he : (fun w => brownianStaticPredictableSum W.B T H (2^l) ((),w)) =ᵐ[W.law]
      (fun w => F (brownianFullPast W.B s w)*actualCurvatureDyadicIntervalSum W β s t l w) := by
    filter_upwards [rawPastCurvature_actual W β] with w hw
    rw [brownianStaticPredictableSum,predictableGaussianSum_eq_range_sum,
      actualCurvatureDyadicIntervalSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (F (brownianFullPast W.B s w)*rawPastCurvature β (T k)
      (brownianFullPast W.B (T k) w))*_ = _
    have hraw := hw (T k)
    change rawPastCurvature β (T k) (brownianFullPast W.B (T k) w) = _ at hraw
    rw [hraw]
    dsimp only [brownianMeshIncrement,T]
    ring
  have hT0 : T 0 = s := by simp [T]
  have hTn : T (2^l) = t := by
    simp only [T,Nat.cast_pow,Nat.cast_ofNat,div_self (by positivity : (2 : ℝ≥0)^l ≠ 0),
      mul_one,add_tsub_cancel_of_le hst]
  rw [integral_unit_prod,integral_unit_prod,hTn,hT0] at hm
  rw [integral_congr_ae (he.mono fun w hw => congrArg (fun x : ℝ => x^2) hw)] at hm
  rw [integral_congr_ae (he.mono fun w hw => congrArg (fun x : ℝ => x^4) hw)] at hm
  exact hm.2.2

theorem actualIncrement_past_weighted_moments_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0) (hst : s ≤ t)
    (F : (Iic s → ℝ) → ℝ) (hF : Measurable F) (hFcap : ∀ p, |F p| ≤ 1) :
    (∫ w, (F (brownianFullPast W.B s w)*actualParisiMagnetizationIncrement W β s t w)^2 ∂W.law) ≤
        ((t : ℝ)-s)*(∫ w, F (brownianFullPast W.B s w)^2 ∂W.law) ∧
      (∫ w, (F (brownianFullPast W.B s w)*actualParisiMagnetizationIncrement W β s t w)^4 ∂W.law) ≤
        3*((t : ℝ)-s)^2*(∫ w, F (brownianFullPast W.B s w)^2 ∂W.law) := by
  let := W.isProbability
  let f := fun w => F (brownianFullPast W.B s w)
  let S := actualCurvatureDyadicIntervalSum W β s t
  let Y := actualParisiMagnetizationIncrement W β s t
  have hfm : Measurable f := hF.comp (Measurable.of_eval (fun u : Iic s => W.measurable u))
  have hfc (w) : |f w| ≤ 1 := hFcap _
  have hS (l) : MemLp (S l) 2 W.law := by
    convert (memLp_actualCurvatureLeftSum W β (intervalDyadicGrid s t) 2 l).sub
      (memLp_actualCurvatureLeftSum W β (intervalDyadicGrid s t) 1 l) using 1
    funext w
    exact actualCurvatureDyadicIntervalSum_eq_sub W β s t l w
  have hbounded (p : ℝ≥0∞) (Z : Ω → ℝ) (hZ : MemLp Z p W.law) :
      MemLp (fun w => f w*Z w) p W.law := by
    apply hZ.mono (hfm.aestronglyMeasurable.mul hZ.aestronglyMeasurable)
    apply ae_of_all
    intro w
    change |f w*Z w| ≤ |Z w|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hfc w) (abs_nonneg _)).trans_eq (one_mul _)
  have hS' (l) := hbounded 2 (S l) (hS l)
  have hY := actualIncrement_memLp W β s t 2
  have hY' := hbounded 2 Y hY
  have hY4 := integrable_fourth_of_memLp _ _
    (hbounded 4 Y (actualIncrement_memLp W β s t 4))
  have hS4 (l) : Integrable (fun w => (f w*S l w)^4) W.law := by
    apply ((actualCurvatureDyadicIntervalSum_fourth_le W β s t hst l).1).mono'
      ((hfm.aestronglyMeasurable.mul (hS l).aestronglyMeasurable).pow 4)
    apply ae_of_all
    intro w
    change ‖(f w*S l w)^4‖ ≤ S l w^4
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (f w*S l w)^4),mul_pow]
    have hf2 : f w^2 ≤ 1 := by nlinarith [hfc w,sq_abs (f w),abs_nonneg (f w)]
    have hf4 : f w^4 ≤ 1 := by nlinarith [sq_nonneg (f w)]
    exact (mul_le_mul_of_nonneg_right hf4 (by positivity)).trans_eq (one_mul _)
  have hlim : Tendsto (fun l => ∫ w, (f w*S l w-f w*Y w)^2 ∂W.law) atTop (𝓝 0) := by
    apply squeeze_zero (fun l => integral_nonneg fun w => sq_nonneg _)
      (fun l => integral_mono_ae ((hS' l).sub hY').integrable_sq
        ((hS l).sub hY).integrable_sq (ae_of_all _ fun w => ?_))
      (actual_curvature_dyadic_interval_meanSquare_tendsto W β hβ s t hst)
    have hf2 : f w^2 ≤ 1 := by nlinarith [hfc w,sq_abs (f w),abs_nonneg (f w)]
    change (f w*S l w-f w*Y w)^2 ≤ (S l w-Y w)^2
    calc
      _ = f w^2*(S l w-Y w)^2 := by ring
      _ ≤ 1*(S l w-Y w)^2 := mul_le_mul_of_nonneg_right hf2 (sq_nonneg _)
      _ = _ := one_mul _
  have hnorm (Z : Ω → ℝ) (hZ : MemLp Z 2 W.law) :
      ‖hZ.toLp Z‖^2 = ∫ w, Z w^2 ∂W.law := by
    have hz : MemLp (0 : Ω → ℝ) 2 W.law := memLp_const 0
    have he := norm_toLp_difference_sq_eq_integral hZ hz
    rw [MemLp.toLp_zero,sub_zero] at he
    simpa only [Pi.zero_apply,sub_zero] using he
  have hsecond : Tendsto (fun l => ∫ w, (f w*S l w)^2 ∂W.law) atTop
      (𝓝 (∫ w, (f w*Y w)^2 ∂W.law)) := by
    simpa only [hnorm] using (tendsto_toLp_of_meanSquare hS' hY' hlim).norm.pow 2
  have hb := actualCurvatureDyadicIntervalSum_past_weighted_moments_le W β s t hst F hF hFcap
  refine ⟨le_of_tendsto hsecond (Eventually.of_forall fun l => (hb l).1), ?_⟩
  exact fourthMoment_le_const_of_meanSquare W.law _ _ _
    (mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _))
    hS' hY' hS4 hY4 hlim (fun l => (hb l).2)

theorem actualIncrement_fourth_le_three (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, actualParisiMagnetizationIncrement W β s t w^4 ∂W.law) ≤ 3*((t : ℝ)-s)^2 := by
  let := W.isProbability
  simpa using (actualIncrement_past_weighted_moments_le W β hβ s t hst
    (fun _ => 1) measurable_const (by simp)).2

theorem normalizedIncrement_past_weighted_moments_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0) (hst : s ≤ t)
    (F : (Iic s → ℝ) → ℝ) (hF : Measurable F) (hFcap : ∀ p, |F p| ≤ 1) :
    (∫ w, (F (brownianFullPast W.B s w)*normalizedIncrement W β s t w)^2 ∂W.law) ≤
        (((t : ℝ)-s)*(∫ w, F (brownianFullPast W.B s w)^2 ∂W.law)) /
          (actualParisiPosteriorIntervalScale W β s t : ℝ)^2 ∧
      (∫ w, (F (brownianFullPast W.B s w)*normalizedIncrement W β s t w)^4 ∂W.law) ≤
        (3*((t : ℝ)-s)^2*(∫ w, F (brownianFullPast W.B s w)^2 ∂W.law)) /
          (actualParisiPosteriorIntervalScale W β s t : ℝ)^4 := by
  have hm := actualIncrement_past_weighted_moments_le W β hβ s t hst F hF hFcap
  constructor
  · simpa only [normalizedIncrement,←mul_div_assoc,div_pow,integral_div] using
      div_le_div_of_nonneg_right hm.1
        (sq_nonneg (actualParisiPosteriorIntervalScale W β s t : ℝ))
  · simpa only [normalizedIncrement,←mul_div_assoc,div_pow,integral_div] using
      div_le_div_of_nonneg_right hm.2
        (by positivity : 0 ≤ (actualParisiPosteriorIntervalScale W β s t : ℝ)^4)

theorem normalizedIncrement_fourth_le_three (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, normalizedIncrement W β s t w^4 ∂W.law) ≤
      3*((t : ℝ)-s)^2/(actualParisiPosteriorIntervalScale W β s t : ℝ)^4 := by
  let := W.isProbability
  simpa using (normalizedIncrement_past_weighted_moments_le W β hβ s t hst
    (fun _ => 1) measurable_const (by simp)).2

end SKConstants.Completion.N9Y1
