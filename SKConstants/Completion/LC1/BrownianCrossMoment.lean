module

public import SKConstants.Completion.LC1.DriftProjection

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualFullProcess_brownian_cross_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      actualParisiMagnetizationObservable W β (a+v) w * (W.B (a+v) w - W.B a w) ∂W.law) =
    ∫ r in (a:ℝ)..((a+v:ℝ≥0):ℝ), ∫ w,
      F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
        actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  let T := a+v
  let P := boundedDriftPastPath W b a
  let f := F ∘ P
  let M := actualParisiMagnetizationObservable W β
  let Y := actualParisiFullScalarProcess W β
  let d := b.pathDrift W
  let D := b.displacement W a T
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W b a)
  have hfC (w : Ω) : |f w| ≤ C := hFC _
  have hmT : Measurable (M T) := measurable_actualParisiMagnetizationObservable W β T
  have hfM : Measurable (fun w => f w * M T w) := hf.mul hmT
  have hfMC (w : Ω) : |f w * M T w| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul (hfC w) (actualParisiMagnetizationObservable_abs_le W β T w)
      (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _)
  have hd : Measurable (Function.uncurry d) := b.pathDrift_measurable W
  have hdC (r : ℝ) (w : Ω) : |d r w| ≤ (1 : ℝ≥0) := b.pathDrift_bound W r w
  have hiD : Integrable D W.law := by
    apply Integrable.of_bound (b.displacement_measurable W a T).aestronglyMeasurable
      ((b.bound:ℝ) * |(T:ℝ)-(a:ℝ)|)
    exact ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact b.displacement_bound W a T w)
  have hiWeightedD : Integrable (fun w => (f w * M T w) * D w) W.law :=
    hiD.bdd_mul hfM.aestronglyMeasurable
      (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hfMC w))
  have hiCoord (t : ℝ≥0) : Integrable (fun w => f w * actualCoordinateObservable W β t w) W.law :=
    (integrable_actualCoordinateObservable W β t).bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hfC w))
  have hiInitial : Integrable (fun w => f w * Y a w * M T w) W.law := by
    have h := (b.solution_integrable W a).bdd_mul hfM.aestronglyMeasurable
      (ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hfMC w))
    convert h using 1
    funext w
    change f w * Y a w * M T w = f w * M T w * Y a w
    ring
  let rate : ℝ → Ω → ℝ := fun r w => f w * actualCoordinateRate β r.toNNReal (Y r.toNNReal w)
  let killed : ℝ → Ω → ℝ := fun r w => f w * d r w * M r.toNNReal w
  have hY : Measurable (fun p : ℝ × Ω => Y p.1.toNNReal p.2) := by
    simpa only [zero_add] using measurable_fullScalar_real_shift W β 0
  have hM : Measurable (fun p : ℝ × Ω => M p.1.toNNReal p.2) := by
    have hp : Measurable (fun p : ℝ × Ω => ((p.1.toNNReal:ℝ), Y p.1.toNNReal p.2)) :=
      (measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)).prodMk hY
    convert (continuous_actualParisiFullMagnetization β).measurable.comp hp using 1
    funext p
    rfl
  have hmRate : Measurable (Function.uncurry rate) := by
    have hr := measurable_actualCoordinateRate_process W β 0
    simp only [zero_add, NNReal.coe_zero] at hr
    exact (hf.comp measurable_snd).mul hr
  have hmKilled : Measurable (Function.uncurry killed) := ((hf.comp measurable_snd).mul hd).mul hM
  have hbRate (r : ℝ) (w : Ω) : |rate r w| ≤ (2*C : ℝ≥0) := by
    change |f w * actualCoordinateRate β r.toNNReal (Y r.toNNReal w)| ≤ _
    rw [abs_mul, NNReal.coe_mul, NNReal.coe_ofNat]
    have h := mul_le_mul (hfC w) (actualCoordinateRate_abs_le β r.toNNReal (Y r.toNNReal w))
      (abs_nonneg _) C.coe_nonneg
    nlinarith
  have hbKilled (r : ℝ) (w : Ω) : |killed r w| ≤ C := by
    have hb : |f w * d r w| ≤ C := by
      rw [abs_mul]
      exact (mul_le_mul (hfC w) (hdC r w) (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _)
    exact (abs_mul _ _).trans_le ((mul_le_mul hb
      (actualParisiMagnetizationObservable_abs_le W β r.toNNReal w)
      (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _))
  have hRateTime := bounded_expected_intervalIntegrable W.law rate hmRate (2*C) hbRate a T
  have hKilledTime := bounded_expected_intervalIntegrable W.law killed hmKilled C hbKilled a T
  have hDrift : (∫ w, (f w * M T w) * D w ∂W.law) =
      ∫ r in (a:ℝ)..(T:ℝ), ∫ w, killed r w ∂W.law := by
    change (∫ w, (f w * M T w) * (∫ r in (a:ℝ)..(T:ℝ), d r w) ∂W.law) = _
    rw [bounded_signed_interval_expectation_swap W.law a T (fun w => f w*M T w) hfM C hfMC d hd 1 hdC]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_le_coe.mpr (le_add_of_nonneg_right bot_le : a ≤ T))] at hr
    have hr0 : 0 ≤ r := a.coe_nonneg.trans hr.1
    have hac : a ≤ r.toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hr0]
      exact hr.1
    have hcT : r.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hr0]
      exact hr.2
    calc
      _ = ∫ w, f w * d r w * M T w ∂W.law := by
        apply integral_congr_ae
        exact ae_of_all _ (fun w => by ring)
      _ = ∫ w, f w * d r w * M r.toNNReal w ∂W.law :=
        actualFullProcess_drift_projection W β hβ a r.toNNReal T hac hcT F hF C hFC
      _ = _ := rfl
  have hInitial := actualFullProcess_initial_coordinate_projection W β hβ a T
    (le_add_of_nonneg_right bot_le) F hF C hFC
  change (∫ w, f w * Y a w * M T w ∂W.law) =
    ∫ w, f w * actualCoordinateObservable W β a w ∂W.law at hInitial
  have hCoord := actualFullProcess_coordinate_generator_test W β hβ a v F hF C hFC
  change (∫ w, f w * (actualCoordinateObservable W β T w - actualCoordinateObservable W β a w) ∂W.law) =
    ∫ r in (a:ℝ)..(T:ℝ), ∫ w, rate r w ∂W.law at hCoord
  have hRateSub (r : ℝ) : (∫ w, rate r w ∂W.law) - (∫ w, killed r w ∂W.law) =
      ∫ w, f w * actualParisiFullCurvature β r.toNNReal (Y r.toNNReal w) ∂W.law := by
    have hiR : Integrable (rate r) W.law := Integrable.of_bound
      (hmRate.comp measurable_prodMk_left).aestronglyMeasurable (2*C) (ae_of_all _ (hbRate r))
    have hiK : Integrable (killed r) W.law := Integrable.of_bound
      (hmKilled.comp measurable_prodMk_left).aestronglyMeasurable C (ae_of_all _ (hbKilled r))
    rw [← integral_sub hiR hiK]
    apply integral_congr_ae
    apply ae_of_all
    intro w
    change f w * (actualParisiFullCurvature β r.toNNReal (Y r.toNNReal w) +
      M r.toNNReal w * d r w) - f w * d r w * M r.toNNReal w = _
    ring
  calc
    _ = ∫ w, f w * actualCoordinateObservable W β T w - f w * Y a w * M T w -
        (f w * M T w) * D w ∂W.law := by
      apply integral_congr_ae
      filter_upwards [b.solution_increment W a v] with w hw
      change f w * M T w * (W.B T w-W.B a w) =
        f w * (Y T w * M T w) - f w * Y a w * M T w - (f w * M T w) * D w
      change Y T w = Y a w + (W.B T w-W.B a w) + D w at hw
      rw [hw]
      ring
    _ = ((∫ w, f w * actualCoordinateObservable W β T w ∂W.law) -
        (∫ w, f w * Y a w * M T w ∂W.law)) -
        (∫ w, (f w * M T w) * D w ∂W.law) := by
      rw [integral_sub (f:=fun w => f w * actualCoordinateObservable W β T w - f w * Y a w * M T w)
        (g:=fun w => (f w * M T w) * D w) ((hiCoord T).sub hiInitial) hiWeightedD,
        integral_sub (hiCoord T) hiInitial]
    _ = ((∫ w, f w * actualCoordinateObservable W β T w ∂W.law) -
        (∫ w, f w * actualCoordinateObservable W β a w ∂W.law)) -
        (∫ w, (f w * M T w) * D w ∂W.law) := by rw [hInitial]
    _ = (∫ w, f w * (actualCoordinateObservable W β T w - actualCoordinateObservable W β a w) ∂W.law) -
        (∫ w, (f w * M T w) * D w ∂W.law) := by
      rw [show (fun w => f w * (actualCoordinateObservable W β T w - actualCoordinateObservable W β a w)) =
        (fun w => f w * actualCoordinateObservable W β T w - f w * actualCoordinateObservable W β a w) by
          funext w; ring, integral_sub (hiCoord T) (hiCoord a)]
    _ = (∫ r in (a:ℝ)..(T:ℝ), ∫ w, rate r w ∂W.law) -
        (∫ r in (a:ℝ)..(T:ℝ), ∫ w, killed r w ∂W.law) := by rw [hCoord, hDrift]
    _ = ∫ r in (a:ℝ)..(T:ℝ), ((∫ w, rate r w ∂W.law) - (∫ w, killed r w ∂W.law)) :=
      (intervalIntegral.integral_sub hRateTime hKilledTime).symm
    _ = _ := intervalIntegral.integral_congr (fun r _ => hRateSub r)

end SKConstants.Completion.LC1
