module

public import SKConstants.Completion.LC1.CoordinatePast

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

lemma nnreal_shift_intervalIntegral (g : ℝ≥0 → ℝ) (a v : ℝ≥0) :
    (∫ u in 0..(v:ℝ), g (a+u.toNNReal)) =
      ∫ r in (a:ℝ)..((a+v:ℝ≥0):ℝ), g r.toNNReal := by
  calc
    _ = ∫ u in 0..(v:ℝ), g (((a:ℝ)+u).toNNReal) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le v.coe_nonneg] at hu
      change g (a+u.toNNReal) = g (((a:ℝ)+u).toNNReal)
      congr 1
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ hu.1,
        Real.coe_toNNReal _ (add_nonneg a.coe_nonneg hu.1)]
    _ = _ := by
      simpa only [add_zero, NNReal.coe_add] using
        intervalIntegral.integral_comp_add_left (fun r => g r.toNNReal) (a:ℝ) (a:=0) (b:=(v:ℝ))

lemma bounded_expected_intervalIntegrable (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℝ → Ω → ℝ) (hg : Measurable (Function.uncurry g)) (C : ℝ≥0)
    (hC : ∀ r w, |g r w| ≤ C) (s t : ℝ) :
    IntervalIntegrable (fun r => ∫ w, g r w ∂P) volume s t := by
  apply intervalIntegrable_iff.mpr
  exact (bounded_interval_prod_integrable P s t g hg C hC).integral_prod_left

lemma actualFullProcess_coordinate_generator_test_side_absolute
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (hside : a+v ≤ parisiEquilibriumPhysicalEndpoint β ∨ parisiEquilibriumPhysicalEndpoint β ≤ a)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w) ∂W.law) =
      ∫ r in (a:ℝ)..((a+v:ℝ≥0):ℝ), ∫ w,
        F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
          actualCoordinateRate β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law := by
  exact (actualFullProcess_coordinate_generator_test_side W β hβ a v hside F hF C hFC).trans
    (nnreal_shift_intervalIntegral
      (fun r => ∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
        actualCoordinateRate β r (actualParisiFullScalarProcess W β r w) ∂W.law) a v)

theorem actualFullProcess_coordinate_generator_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w) ∂W.law) =
      ∫ r in (a:ℝ)..((a+v:ℝ≥0):ℝ), ∫ w,
        F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
          actualCoordinateRate β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law := by
  let := W.isProbability
  let V := parisiEquilibriumPhysicalEndpoint β
  by_cases hav : a+v ≤ V
  · exact actualFullProcess_coordinate_generator_test_side_absolute W β hβ a v (Or.inl hav) F hF C hFC
  by_cases ha : V ≤ a
  · exact actualFullProcess_coordinate_generator_test_side_absolute W β hβ a v (Or.inr ha) F hF C hFC
  have haV : a ≤ V := (lt_of_not_ge ha).le
  have hVH : V ≤ a+v := (lt_of_not_ge hav).le
  let d := V-a
  let e := a+v-V
  have had : a+d=V := add_tsub_cancel_of_le haV
  have hVe : V+e=a+v := add_tsub_cancel_of_le hVH
  let b := actualParisiFullScalarDrift β
  let P := boundedDriftPastPath W b a
  let f := F ∘ P
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W b a)
  let G := F ∘ scalarContinuousPathRestrict a V haV
  have hG : Measurable G := hF.comp (measurable_scalarContinuousPathRestrict a V haV)
  have Hpre := actualFullProcess_coordinate_generator_test_side_absolute W β hβ a d
    (Or.inl (by rw [had])) F hF C hFC
  rw [had] at Hpre
  have Hpost := actualFullProcess_coordinate_generator_test_side_absolute W β hβ V e
    (Or.inr le_rfl) G hG C (fun p => hFC _)
  rw [hVe] at Hpost
  have hchange (J : Ω → ℝ) : (∫ w, G (boundedDriftPastPath W b V w) * J w ∂W.law) =
      ∫ w, f w * J w ∂W.law := by
    apply integral_congr_ae
    filter_upwards [boundedDriftPastPath_restrict W b a V haV] with w hw
    dsimp only [G, Function.comp_apply]
    rw [hw]
    rfl
  change (∫ w, G (boundedDriftPastPath W b V w) *
    (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β V w) ∂W.law) =
    ∫ r in (V:ℝ)..((a+v:ℝ≥0):ℝ), ∫ w, G (boundedDriftPastPath W b V w) *
      actualCoordinateRate β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law at Hpost
  simp_rw [hchange] at Hpost
  have hi (s t : ℝ≥0) : Integrable (fun w => f w *
      (actualCoordinateObservable W β t w - actualCoordinateObservable W β s w)) W.law := by
    apply ((integrable_actualCoordinateObservable W β t).sub
      (integrable_actualCoordinateObservable W β s)).bdd_mul hf.aestronglyMeasurable
    exact ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hFC _)
  let rate : ℝ → Ω → ℝ := fun r w => f w *
    actualCoordinateRate β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w)
  have hmRate : Measurable (Function.uncurry rate) := by
    have hr := measurable_actualCoordinateRate_process W β 0
    simp only [zero_add, NNReal.coe_zero] at hr
    exact (hf.comp measurable_snd).mul hr
  have hbRate (r : ℝ) (w : Ω) : |rate r w| ≤ (2*C : ℝ≥0) := by
    change |f w * actualCoordinateRate β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w)| ≤ _
    rw [abs_mul, NNReal.coe_mul, NNReal.coe_ofNat]
    have hfC : |f w| ≤ C := hFC (P w)
    have hmul := mul_le_mul hfC
      (actualCoordinateRate_abs_le β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w))
      (abs_nonneg _) C.coe_nonneg
    nlinarith
  have hir (s t : ℝ) := bounded_expected_intervalIntegrable W.law rate hmRate (2*C) hbRate s t
  calc
    _ = ∫ w, f w * (actualCoordinateObservable W β V w - actualCoordinateObservable W β a w) +
        f w * (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β V w) ∂W.law := by
      apply integral_congr_ae
      exact ae_of_all _ (fun w => by change f w * _ = _; ring)
    _ = (∫ w, f w * (actualCoordinateObservable W β V w - actualCoordinateObservable W β a w) ∂W.law) +
        (∫ w, f w * (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β V w) ∂W.law) :=
      integral_add (hi a V) (hi V (a+v))
    _ = (∫ r in (a:ℝ)..(V:ℝ), ∫ w, rate r w ∂W.law) +
        (∫ r in (V:ℝ)..((a+v:ℝ≥0):ℝ), ∫ w, rate r w ∂W.law) :=
      congrArg₂ (fun x y : ℝ => x+y) Hpre Hpost
    _ = _ := intervalIntegral.integral_add_adjacent_intervals (hir a V) (hir V (a+v))

end SKConstants.Completion.LC1
