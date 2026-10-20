module

public import SKConstants.Completion.LBase.CurvaturePast
public import SKConstants.Completion.LBase.IntegratedQuadrature

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedLipschitzDrift.solution
set_option maxHeartbeats 500000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma unitLift_measurePreserving (P : Measure Ω) [SFinite P] :
    MeasurePreserving (Prod.mk () : Ω → Unit × Ω) P ((Measure.dirac ()).prod P) :=
  ⟨measurable_const.prodMk measurable_id, (Measure.dirac_prod ()).symm⟩

lemma integral_unit_prod (P : Measure Ω) [SFinite P] (f : Unit × Ω → ℝ) :
    (∫ u, f u ∂(Measure.dirac ()).prod P) = ∫ w, f ((), w) ∂P :=
  ((unitLift_measurePreserving P).integral_comp (measurableEmbedding_prodMk_left ()) f).symm

def actualCurvatureLeftSum (W : BrownianSystem Ω) (β : ℝ)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range (k * 2^l), actualCurvatureProcess W β (G.time l i) w *
    (W.B (G.time l (i+1)) w - W.B (G.time l i) w)

lemma measurable_actualCurvatureLeftSum (W : BrownianSystem Ω) (β : ℝ)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) : Measurable (actualCurvatureLeftSum W β G k l) := by
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_actualCurvatureProcess W β).comp (measurable_const.prodMk measurable_id)).mul
    ((W.measurable _).sub (W.measurable _))

lemma rawCurvatureLeftSum_actual (W : BrownianSystem Ω) (β : ℝ)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) :
    (fun w => brownianContinuousLeftSum W.B (curvaturePastCoefficient β) G k l ((), w)) =ᵐ[W.law]
      actualCurvatureLeftSum W β G k l := by
  filter_upwards [rawPastCurvature_actual W β] with w hw
  rw [brownianContinuousLeftSum, brownianStaticPredictableSum, predictableGaussianSum_eq_range_sum]
  apply Finset.sum_congr rfl
  intro i _
  change rawPastCurvature β _ _ * _ = actualCurvatureProcess W β _ w * _
  exact congrArg (fun x : ℝ => x * (W.B (G.time l (i+1)) w - W.B (G.time l i) w)) (hw _)

theorem memLp_actualCurvatureLeftSum (W : BrownianSystem Ω) (β : ℝ)
    (G : ScalarDyadicNestedGrid) (k l : ℕ) : MemLp (actualCurvatureLeftSum W β G k l) 2 W.law := by
  have h := memLp_brownianStaticPredictableSum (Measure.dirac ()) W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable (G.time l) (G.monotone l)
    (brownianContinuousMeshCoefficient (curvaturePastCoefficient β) (G.time l))
    (fun i => measurable_curvaturePastCoefficient β _) 1
    (fun i u => curvaturePastCoefficient_norm_le β _ u) (k * 2^l)
  exact (h.comp_measurePreserving (unitLift_measurePreserving W.law)).ae_eq
    (rawCurvatureLeftSum_actual W β G k l)

lemma curvaturePastCoefficient_continuous_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ u ∂(Measure.dirac ()).prod W.law,
      Continuous (fun t => brownianContinuousCoefficient W.B (curvaturePastCoefficient β) t u) := by
  have ha := (measurePreserving_snd (μ := Measure.dirac ()) (ν := W.law)).quasiMeasurePreserving.ae
    (rawPastCurvature_actual W β)
  have hc := (measurePreserving_snd (μ := Measure.dirac ()) (ν := W.law)).quasiMeasurePreserving.ae
    (actualCurvatureProcess_continuous_ae W β)
  filter_upwards [ha, hc] with u hu huc
  have he : (fun t => brownianContinuousCoefficient W.B (curvaturePastCoefficient β) t u) =
      fun t : ℝ≥0 => actualCurvatureProcess W β t u.2 := funext hu
  rw [he]
  exact huc.comp NNReal.continuous_coe

theorem actual_curvature_bracket_mean (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0) :
    (∫ u, brownianContinuousQuadraticVariation W.B (curvaturePastCoefficient β) T u
      ∂(Measure.dirac ()).prod W.law) =
      ∫ r in (0 : ℝ)..T, actualParisiFullSusceptibilitySquareExpected W β r := by
  rw [integral_unit_prod]
  have he : (fun w => brownianContinuousQuadraticVariation W.B (curvaturePastCoefficient β) T ((), w)) =ᵐ[W.law]
      (fun w => ∫ r in (0 : ℝ)..T, (actualCurvatureProcess W β r w)^2) := by
    filter_upwards [rawPastCurvature_actual W β] with w hw
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le T.coe_nonneg] at hr
    change (rawPastCurvature β r.toNNReal _)^2 = _
    have hh := hw r.toNNReal
    rw [Real.coe_toNNReal r hr.1] at hh
    exact congrArg (fun x : ℝ => x^2) hh
  rw [integral_congr_ae he]
  exact LC1.bounded_interval_expectation_swap W.law 0 T
    (fun r w => (actualCurvatureProcess W β r w)^2)
    ((measurable_actualCurvatureProcess W β).pow_const 2) 1 (fun r w => by
      change |(actualCurvatureProcess W β r w)^2| ≤ (1 : ℝ)
      rw [abs_pow]
      nlinarith [actualCurvatureProcess_abs_le W β r w, abs_nonneg (actualCurvatureProcess W β r w)])

theorem actual_curvature_leftSum_secondMoment_tendsto (W : BrownianSystem Ω) (β : ℝ)
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k * 2^l → (G.time l (i+1) : ℝ) - G.time l i ≤ δ l) :
    Tendsto (fun l => ∫ w, (actualCurvatureLeftSum W β G k l w)^2 ∂W.law) atTop
      (𝓝 (∫ r in (0 : ℝ)..(G.time 0 k : ℝ), actualParisiFullSusceptibilitySquareExpected W β r)) := by
  have h := brownianContinuousLeftSum_secondMoment_tendsto (Measure.dirac ()) W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable (curvaturePastCoefficient β)
    (measurable_curvaturePastCoefficient β) 1 (curvaturePastCoefficient_norm_le β)
    (curvaturePastCoefficient_continuous_ae W β) G k δ hδ hwidth
  rw [actual_curvature_bracket_mean W β] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro l
  dsimp only
  rw [integral_unit_prod]
  exact integral_congr_ae ((rawCurvatureLeftSum_actual W β G k l).mono (fun w hw => congrArg (fun x : ℝ => x^2) hw))

end SKConstants.Completion.LBase
