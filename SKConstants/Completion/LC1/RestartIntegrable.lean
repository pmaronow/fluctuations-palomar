module

public import SKConstants.Completion.LC1.IntegrableTests

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem boundedDrift_restart_integral_integrable
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (a v : ℝ≥0)
    (H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ) (hH : Measurable H)
    (hHi : Integrable (fun w => H (boundedDriftPastPath W b a w,
      boundedDriftRestartPath W b a v w)) W.law) :
    (∫ w, H (boundedDriftPastPath W b a w, boundedDriftRestartPath W b a v w) ∂W.law) =
      ∫ past, ∫ w, H (past, boundedDriftRestartCallback b a v
        (past, brownianFinitePath W v w)) ∂W.law
        ∂W.law.map (boundedDriftPastPath W b a) := by
  let := W.isProbability
  let μ := W.law.map (boundedDriftPastPath W b a)
  let ν := W.law.map (brownianFinitePath W v)
  let J : ScalarContinuousPath a × ScalarContinuousPath v →
      ScalarContinuousPath a × ScalarContinuousPath v :=
    fun p => (p.1, boundedDriftRestartCallback b a v p)
  have hJ : Measurable J := measurable_fst.prodMk (measurable_boundedDriftRestartCallback b a v)
  have hP := (measurable_boundedDriftPastPath W b a).prodMk
    (measurable_boundedDriftRestartPath W b a v)
  have hiMap : Integrable H (W.law.map (fun w =>
      (boundedDriftPastPath W b a w, boundedDriftRestartPath W b a v w))) :=
    (integrable_map_measure hH.aestronglyMeasurable hP.aemeasurable).mpr hHi
  rw [boundedDriftPast_restart_jointLaw] at hiMap
  have hi : Integrable (H ∘ J) (μ.prod ν) :=
    (integrable_map_measure hH.aestronglyMeasurable hJ.aemeasurable).mp hiMap
  rw [← integral_map hP.aemeasurable hH.aestronglyMeasurable,
    boundedDriftPast_restart_jointLaw, integral_map hJ.aemeasurable hH.aestronglyMeasurable]
  change (∫ p, (H ∘ J) p ∂μ.prod ν) = _
  rw [integral_prod (H ∘ J) hi]
  apply integral_congr_ae
  exact ae_of_all _ fun past =>
    integral_map (measurable_brownianFinitePath W v).aemeasurable
      ((hH.comp (measurable_const.prodMk
        ((measurable_boundedDriftRestartCallback b a v).comp
          (measurable_const.prodMk measurable_id)))).aestronglyMeasurable)

theorem boundedDrift_restart_observable_test_integrable
    (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) (a v : ℝ≥0)
    (F : ScalarContinuousPath a → ℝ) (hF : Measurable F)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hi : Integrable (fun w => F (boundedDriftPastPath W b a w) *
      φ (b.solution W.driver (a+v) w)) W.law) :
    (∫ w, F (boundedDriftPastPath W b a w) * φ (b.solution W.driver (a+v) w) ∂W.law) =
      ∫ past, F past * (∫ w, φ (past ⟨a,a.coe_nonneg,le_rfl⟩ +
        (SKConstants.BoundedLipschitzDrift.translated b a (past ⟨a,a.coe_nonneg,le_rfl⟩)).solution
          W.driver v w) ∂W.law) ∂W.law.map (boundedDriftPastPath W b a) := by
  let H : ScalarContinuousPath a × ScalarContinuousPath v → ℝ :=
    fun p => F p.1 * φ (p.2 ⟨v,v.coe_nonneg,le_rfl⟩)
  have hH : Measurable H := (hF.comp measurable_fst).mul
    (hφ.comp ((ContinuousMap.measurable_eval _).comp measurable_snd))
  have he : (fun w => F (boundedDriftPastPath W b a w) * φ (b.solution W.driver (a+v) w)) =ᵐ[W.law]
      (fun w => H (boundedDriftPastPath W b a w,boundedDriftRestartPath W b a v w)) := by
    filter_upwards [boundedDriftRestartPath_version W b a v] with w hw
    change _ = F (boundedDriftPastPath W b a w) *
      φ (boundedDriftRestartPath W b a v w ⟨v,v.coe_nonneg,le_rfl⟩)
    rw [hw]
    rfl
  rw [integral_congr_ae he, boundedDrift_restart_integral_integrable W b a v H hH (hi.congr he)]
  apply integral_congr_ae
  apply ae_of_all
  intro past
  change (∫ w, F past * φ (boundedDriftRestartCallback b a v
    (past,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩) ∂W.law) = _
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [boundedDriftRestartCallback_fresh_version W b a v past] with w hw
  rw [hw]
  rfl

end SKConstants.Completion.LC1
