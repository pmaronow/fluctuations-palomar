module

public import SKConstants.Completion.LC1.CoordinateGenerator

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]

def actualCoordinateObservable (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) (w : Ω) : ℝ :=
  actualParisiFullScalarProcess W β t w * actualParisiMagnetizationObservable W β t w

lemma integrable_actualCoordinateObservable (W : BrownianSystem Ω) (β : ℝ) (t : ℝ≥0) :
    Integrable (actualCoordinateObservable W β t) W.law := by
  apply ((actualParisiFullScalarDrift β).solution_integrable W t).mul_bdd
    (measurable_actualParisiMagnetizationObservable W β t).aestronglyMeasurable
  exact ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact actualParisiMagnetizationObservable_abs_le W β t w)

lemma measurable_fullScalar_real_shift (W : BrownianSystem Ω) (β : ℝ) (a : ℝ≥0) :
    Measurable (fun p : ℝ × Ω => actualParisiFullScalarProcess W β (a+p.1.toNNReal) p.2) := by
  have hy : Measurable (fun p : ℝ≥0 × Ω =>
      (actualParisiFullScalarDrift β).solution W.driver p.1 p.2) := progressive_joint_measurable _
    ((actualParisiFullScalarDrift β).solution_progressive _ W.driver_progressive)
  simpa only [Function.comp_def, actualParisiFullScalarProcess, Pi.add_apply] using
    hy.comp ((measurable_const.add (measurable_real_toNNReal.comp
      (measurable_fst : Measurable (Prod.fst : ℝ × Ω → ℝ)))).prodMk measurable_snd)

lemma measurable_actualCoordinateRate_process (W : BrownianSystem Ω) (β : ℝ) (a : ℝ≥0) :
    Measurable (fun p : ℝ × Ω => actualCoordinateRate β (a+p.1.toNNReal)
      (actualParisiFullScalarProcess W β (a+p.1.toNNReal) p.2)) := by
  have ht : Measurable (fun p : ℝ × Ω => (a:ℝ)+(p.1.toNNReal:ℝ)) :=
    measurable_const.add (measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst))
  simpa only [Function.comp_def, Function.uncurry_def] using
    (measurable_actualCoordinateRate β).comp (ht.prodMk (measurable_fullScalar_real_shift W β a))

lemma integrable_actualCoordinateRate_timeIntegral (W : BrownianSystem Ω) (β : ℝ) (a v : ℝ≥0) :
    Integrable (fun w => ∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal)
      (actualParisiFullScalarProcess W β (a+u.toNNReal) w)) W.law := by
  let := W.isProbability
  apply Integrable.of_bound
    (measurable_time_integral (Ω:=Ω) (f:=fun u w => actualCoordinateRate β (a+u.toNNReal)
      (actualParisiFullScalarProcess W β (a+u.toNNReal) w))
      (measurable_actualCoordinateRate_process W β a) 0 v).aestronglyMeasurable
    (2 * |(v:ℝ)|)
  exact ae_of_all _ (fun w => by
    simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f:=fun u => actualCoordinateRate β (a+u.toNNReal) (actualParisiFullScalarProcess W β (a+u.toNNReal) w))
      (C:=2) (a:=0) (b:=(v:ℝ))
      (fun u _ => by rw [Real.norm_eq_abs]; exact actualCoordinateRate_abs_le β _ _))

lemma actualCoordinateResidual_original_version (W : BrownianSystem Ω) (β : ℝ) (a v : ℝ≥0) :
    (fun w => actualCoordinateResidual β a v
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w,
        boundedDriftRestartPath W (actualParisiFullScalarDrift β) a v w)) =ᵐ[W.law]
      (fun w => actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w -
        ∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal)
          (actualParisiFullScalarProcess W β (a+u.toNNReal) w)) := by
  filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) a,
    boundedDriftRestartPath_version W (actualParisiFullScalarDrift β) a v] with w hp hr
  unfold actualCoordinateResidual
  rw [hp, hr]
  change actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w - _ = _
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le v.coe_nonneg] at hu
  change actualCoordinateRate β (a+u.toNNReal)
    (boundedDriftRestartPath W (actualParisiFullScalarDrift β) a v w
      (projIcc 0 (v:ℝ) v.coe_nonneg u)) = _
  rw [projIcc_of_mem _ hu, hr]
  have huN : (⟨u,hu.1⟩:ℝ≥0) = u.toNNReal :=
    NNReal.coe_injective (Real.coe_toNNReal _ hu.1).symm
  rw [huN]
  rfl

theorem actualFullProcess_coordinate_generator_test_side
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (hside : a+v ≤ parisiEquilibriumPhysicalEndpoint β ∨ parisiEquilibriumPhysicalEndpoint β ≤ a)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
      (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w) ∂W.law) =
      ∫ u in 0..(v:ℝ), ∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) a w) *
        actualCoordinateRate β (a+u.toNNReal) (actualParisiFullScalarProcess W β (a+u.toNNReal) w) ∂W.law := by
  let := W.isProbability
  let b := actualParisiFullScalarDrift β
  let P := boundedDriftPastPath W b a
  let f := F ∘ P
  let R : Ω → ℝ := fun w => ∫ u in 0..(v:ℝ), actualCoordinateRate β (a+u.toNNReal)
    (actualParisiFullScalarProcess W β (a+u.toNNReal) w)
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W b a)
  have hfB : ∀ᵐ w ∂W.law, ‖f w‖ ≤ C := ae_of_all _ (fun w => by rw [Real.norm_eq_abs]; exact hFC _)
  have hiC := (integrable_actualCoordinateObservable W β (a+v)).sub
    (integrable_actualCoordinateObservable W β a)
  have hiR := integrable_actualCoordinateRate_timeIntegral W β a v
  have hi : Integrable (fun w => f w *
      (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w - R w)) W.law :=
    (hiC.sub hiR).bdd_mul hf.aestronglyMeasurable hfB
  let H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ :=
    fun p => F p.1 * actualCoordinateResidual β a v p
  have hH : Measurable H := (hF.comp measurable_fst).mul (measurable_actualCoordinateResidual β a v)
  have he : (fun w => H (P w, boundedDriftRestartPath W b a v w)) =ᵐ[W.law]
      (fun w => f w * (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w - R w)) := by
    filter_upwards [actualCoordinateResidual_original_version W β a v] with w hw
    change F (P w) * _ = _
    rw [hw]
    rfl
  have hz : (∫ w, f w *
      (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w - R w) ∂W.law) = 0 := by
    rw [← integral_congr_ae he,
      boundedDrift_restart_integral_integrable W b a v H hH (hi.congr he.symm)]
    have hzero (past : ScalarContinuousPath a) :
        (∫ w, H (past,boundedDriftRestartCallback b a v (past,brownianFinitePath W v w)) ∂W.law) = 0 := by
      change (∫ w, F past * actualCoordinateResidual β a v
        (past,boundedDriftRestartCallback b a v (past,brownianFinitePath W v w)) ∂W.law) = 0
      rw [integral_const_mul, actualCoordinateResidual_fresh_mean W β hβ a v hside past, mul_zero]
    simp_rw [hzero]
    exact integral_zero _ _
  have hdiff (w : Ω) : f w *
      (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w - R w) =
      f w * (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w) - f w * R w := by ring
  simp_rw [hdiff] at hz
  rw [integral_sub
    (f:=fun w => f w * (actualCoordinateObservable W β (a+v) w - actualCoordinateObservable W β a w))
    (g:=fun w => f w * R w)
    (hiC.bdd_mul hf.aestronglyMeasurable hfB)
    (hiR.bdd_mul hf.aestronglyMeasurable hfB)] at hz
  exact (sub_eq_zero.mp hz).trans
    (bounded_signed_interval_expectation_swap W.law 0 v f hf C (fun w => hFC _)
      (fun u w => actualCoordinateRate β (a+u.toNNReal) (actualParisiFullScalarProcess W β (a+u.toNNReal) w))
      (measurable_actualCoordinateRate_process W β a) 2 (fun u w => actualCoordinateRate_abs_le β _ _))

end SKConstants.Completion.LC1
