module

public import SKConstants.Completion.N9b.GaussianFourth
public import SKConstants.Completion.NScalar.IntervalIntegral
public import SKConstants.Completion.LFine.ActualSchedule
public import SKConstants.BrownianFullPastPredictable
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N9b
open SKConstantsOAI.ZeroTemperatureSK LBase NScalar LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem brownianStaticPredictableSum_fourth_le {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q) (hmB : ∀ t, Measurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (hcap : ∀ k u, |H k u| ≤ 1) (n : ℕ) :
    Integrable (fun u => brownianStaticPredictableSum B t H n u^4) (P.prod Q) ∧
      (∫ u, brownianStaticPredictableSum B t H n u^4 ∂P.prod Q) ≤
        6*((t n : ℝ)-t 0)*(∫ u, brownianStaticPredictableSum B t H n u^2 ∂P.prod Q) := by
  have hsnd : HasLaw (Prod.snd : A × Ω → Ω) Q (P.prod Q) :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  have hfour := predictableGaussianSum_fourth_le (P.prod Q)
    (fun k u => brownianMeshIncrement B t k u.2) (brownianStaticCoefficient B t H)
    (brownianMeshVariance t) (fun k => (brownianMeshIncrement_hasLaw hB t ht k).comp hsnd)
    (aemeasurable_brownianStaticCoefficient P Q B hB hmB t H hH)
    (fun k => ae_of_all _ fun u => hcap k (u.1,brownianFullPast B (t k) u.2))
    (brownianStaticPredictable_state_indep_increment P Q B hB hmB t ht H hH) n
  have hsum : (∑ k ∈ Finset.range n, (brownianMeshVariance t k : ℝ)) = (t n : ℝ)-t 0 := by
    simp only [brownianMeshVariance, NNReal.coe_sub (ht (Nat.le_succ _))]
    exact Finset.sum_range_sub (fun k => (t k : ℝ)) n
  simpa only [hsum, brownianStaticPredictableSum] using hfour

theorem actualCurvatureDyadicIntervalSum_fourth_le
    (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (hst : s ≤ t) (l : ℕ) :
    Integrable (fun w => actualCurvatureDyadicIntervalSum W β s t l w^4) W.law ∧
      (∫ w, actualCurvatureDyadicIntervalSum W β s t l w^4 ∂W.law) ≤
        6*((t : ℝ)-s)*(∫ w, actualCurvatureDyadicIntervalSum W β s t l w^2 ∂W.law) := by
  let := W.isProbability
  let T : ℕ → ℝ≥0 := fun k => s+(t-s)*((k : ℝ≥0)/2^l)
  have hT : Monotone T := by intro i j hij; dsimp [T]; gcongr
  let H : BrownianStaticPredictableCoefficient Unit T := fun k => curvaturePastCoefficient β (T k)
  have hfour := brownianStaticPredictableSum_fourth_le (Measure.dirac ()) W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable T hT H
    (fun k => measurable_curvaturePastCoefficient β (T k))
    (fun k u => curvaturePastCoefficient_norm_le β (T k) u) (2^l)
  have he : (fun w => brownianStaticPredictableSum W.B T H (2^l) ((),w)) =ᵐ[W.law]
      actualCurvatureDyadicIntervalSum W β s t l := by
    filter_upwards [rawPastCurvature_actual W β] with w hw
    rw [brownianStaticPredictableSum, predictableGaussianSum_eq_range_sum]
    apply Finset.sum_congr rfl
    intro i _
    change rawPastCurvature β (T i) (fun u : Iic (T i) => W.B u.1 w)*_ = _
    rw [hw (T i)]
    rfl
  have hT0 : T 0 = s := by simp [T]
  have hTn : T (2^l) = t := by
    simp only [T, Nat.cast_pow, Nat.cast_ofNat, div_self (by positivity : (2 : ℝ≥0)^l ≠ 0),
      mul_one, add_tsub_cancel_of_le hst]
  have hi : Integrable (fun w => brownianStaticPredictableSum W.B T H (2^l) ((),w)^4) W.law :=
    (unitLift_measurePreserving W.law).integrable_comp_of_integrable hfour.1
  refine ⟨hi.congr (he.mono fun w hw => congrArg (fun x : ℝ => x^4) hw), ?_⟩
  rw [integral_unit_prod, integral_unit_prod, hTn, hT0] at hfour
  have h4 := integral_congr_ae (he.mono fun w hw => congrArg (fun x : ℝ => x^4) hw)
  have h2 := integral_congr_ae (he.mono fun w hw => congrArg (fun x : ℝ => x^2) hw)
  rw [h4, h2] at hfour
  exact hfour.2

theorem fourthMoment_le_of_meanSquare (P : Measure Ω) [IsFiniteMeasure P]
    (S : ℕ → Ω → ℝ) (Y : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hS : ∀ n, MemLp (S n) 2 P) (hY : MemLp Y 2 P)
    (hS4 : ∀ n, Integrable (fun w => S n w^4) P)
    (hY4 : Integrable (fun w => Y w^4) P)
    (hlim : Tendsto (fun n => ∫ w, (S n w-Y w)^2 ∂P) atTop (𝓝 0))
    (hbound : ∀ n, (∫ w, S n w^4 ∂P) ≤ K*(∫ w, S n w^2 ∂P)) :
    (∫ w, Y w^4 ∂P) ≤ K*(∫ w, Y w^2 ∂P) := by
  have hnorm (F : Ω → ℝ) (hF : MemLp F 2 P) :
      ‖hF.toLp F‖^2 = ∫ w, F w^2 ∂P := by
    have hzero : MemLp (0 : Ω → ℝ) 2 P := memLp_const 0
    have he := norm_toLp_difference_sq_eq_integral hF hzero
    rw [MemLp.toLp_zero, sub_zero] at he
    simpa only [Pi.zero_apply, sub_zero] using he
  have hsecond : Tendsto (fun n => ∫ w, S n w^2 ∂P) atTop (𝓝 (∫ w, Y w^2 ∂P)) := by
    simpa only [hnorm] using (tendsto_toLp_of_meanSquare hS hY hlim).norm.pow 2
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_integral_sq
    (fun n => ((hS n).sub hY).integrable_sq) hlim).exists_seq_tendsto_ae
  have hpow : ∀ᵐ w ∂P, Tendsto (fun n => ENNReal.ofReal (S (ns n) w^4)) atTop
      (𝓝 (ENNReal.ofReal (Y w^4))) := by
    filter_upwards [hae] with w hw
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hw.pow 4)
  have hfatou : ENNReal.ofReal (∫ w, Y w^4 ∂P) ≤
      ENNReal.ofReal (K*(∫ w, Y w^2 ∂P)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hY4 (ae_of_all _ fun w => by positivity)]
    calc
      _ = ∫⁻ w, liminf (fun n => ENNReal.ofReal (S (ns n) w^4)) atTop ∂P :=
        lintegral_congr_ae (hpow.mono fun w hw => hw.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ w, ENNReal.ofReal (S (ns n) w^4) ∂P) atTop :=
        lintegral_liminf_le' (fun n => (hS4 (ns n)).aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (K*(∫ w, S (ns n) w^2 ∂P))) atTop := by
        apply Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (hS4 (ns n)) (ae_of_all _ fun w => by positivity)]
        exact ENNReal.ofReal_le_ofReal (hbound (ns n))
      _ = _ := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((hsecond.comp hns.tendsto_atTop).const_mul K)).liminf_eq
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hK (integral_nonneg fun _ => sq_nonneg _))).mp hfatou

theorem actualIncrement_memLp (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (p : ℝ≥0∞) :
    MemLp (actualParisiMagnetizationIncrement W β s t) p W.law := by
  let := W.isProbability
  exact MemLp.of_bound (measurable_actualParisiMagnetizationIncrement W β s t).aestronglyMeasurable
    2 (ae_of_all _ fun w => by
      rw [Real.norm_eq_abs]
      exact actualParisiMagnetizationIncrement_abs_le W β s t w)

theorem actualIncrement_fourth_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, actualParisiMagnetizationIncrement W β s t w^4 ∂W.law) ≤
      6*((t : ℝ)-s)*(∫ w, actualParisiMagnetizationIncrement W β s t w^2 ∂W.law) := by
  let := W.isProbability
  have hS (l) : MemLp (actualCurvatureDyadicIntervalSum W β s t l) 2 W.law := by
    convert (memLp_actualCurvatureLeftSum W β (intervalDyadicGrid s t) 2 l).sub
      (memLp_actualCurvatureLeftSum W β (intervalDyadicGrid s t) 1 l) using 1
    funext w
    exact actualCurvatureDyadicIntervalSum_eq_sub W β s t l w
  exact fourthMoment_le_of_meanSquare W.law _ _ (6*((t : ℝ)-s))
    (mul_nonneg (by norm_num) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))) hS
    (actualIncrement_memLp W β s t 2)
    (fun l => (actualCurvatureDyadicIntervalSum_fourth_le W β s t hst l).1)
    (integrable_fourth_of_memLp _ _ (actualIncrement_memLp W β s t 4))
    (actual_curvature_dyadic_interval_meanSquare_tendsto W β hβ s t hst)
    (fun l => (actualCurvatureDyadicIntervalSum_fourth_le W β s t hst l).2)

def normalizedIncrement (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) : ℝ :=
  actualParisiMagnetizationIncrement W β s t w /
    (actualParisiPosteriorIntervalScale W β s t : ℝ)

theorem measurable_normalizedIncrement (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) :
    Measurable (normalizedIncrement W β s t) :=
  (measurable_actualParisiMagnetizationIncrement W β s t).div_const _

theorem normalizedIncrement_memLp (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (p : ℝ≥0∞) :
    MemLp (normalizedIncrement W β s t) p W.law := by
  unfold normalizedIncrement
  simp_rw [div_eq_mul_inv]
  exact (actualIncrement_memLp W β s t p).mul_const (actualParisiPosteriorIntervalScale W β s t : ℝ)⁻¹

theorem normalizedIncrement_mean_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) : (∫ w, normalizedIncrement W β s t w ∂W.law) = 0 := by
  unfold normalizedIncrement actualParisiMagnetizationIncrement
  rw [integral_div, integral_sub (integrable_actualParisiMagnetizationObservable W β t)
    (integrable_actualParisiMagnetizationObservable W β s),
    actualParisiMagnetizationObservable_mean_zero W β hβ t,
    actualParisiMagnetizationObservable_mean_zero W β hβ s, sub_self, zero_div]

theorem normalizedIncrement_second (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s < t) :
    (∫ w, normalizedIncrement W β s t w^2 ∂W.law) = 1 := by
  have hs : (actualParisiPosteriorIntervalScale W β s t : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ s t hst)).ne'
  have hvar := actualParisiIncrement_secondMoment W β hβ s t hst.le
  change (∫ w, actualParisiMagnetizationIncrement W β s t w^2 ∂W.law) =
    actualParisiFullOverlap W β t-actualParisiFullOverlap W β s at hvar
  simp only [normalizedIncrement, div_pow, integral_div, hvar,
    ← actualParisiPosteriorIntervalScale_sq W β hβ s t hst]
  exact div_self (pow_ne_zero 2 hs)

theorem normalizedIncrement_fourth_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s < t) :
    (∫ w, normalizedIncrement W β s t w^4 ∂W.law) ≤
      6*((t : ℝ)-s)/(actualParisiPosteriorIntervalScale W β s t : ℝ)^2 := by
  let σ : ℝ := actualParisiPosteriorIntervalScale W β s t
  have hs : σ ≠ 0 :=
    (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ s t hst)).ne'
  have hvar := actualParisiIncrement_secondMoment W β hβ s t hst.le
  change (∫ w, actualParisiMagnetizationIncrement W β s t w^2 ∂W.law) =
    actualParisiFullOverlap W β t-actualParisiFullOverlap W β s at hvar
  rw [← actualParisiPosteriorIntervalScale_sq W β hβ s t hst] at hvar
  have hfour := actualIncrement_fourth_le W β hβ s t hst.le
  rw [hvar] at hfour
  simp only [normalizedIncrement, div_pow, integral_div]
  calc
    _ ≤ (6*((t : ℝ)-s)*σ^2)/σ^4 :=
      div_le_div_of_nonneg_right hfour (by positivity)
    _ = _ := by change _ = 6*((t : ℝ)-s)/σ^2; field_simp

end SKConstants.Completion.N9b
