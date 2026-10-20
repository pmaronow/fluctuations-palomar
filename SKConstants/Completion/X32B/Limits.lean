module

public import SKConstants.Completion.X32B.Quadratic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X32B
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto

variable {Ω : Type*} [MeasurableSpace Ω]

def posteriorReal (W : BrownianSystem Ω) (β s : ℝ) (w : Ω) : ℝ :=
  actualParisiFullPosteriorMean W β s.toNNReal w

def curvatureReal (W : BrownianSystem Ω) (β s : ℝ) (w : Ω) : ℝ :=
  LJ.actualCurvature W β s.toNNReal w

attribute [local irreducible] actualParisiFullMagnetization actualParisiFullCurvature
  actualParisiFullScalarDrift

theorem measurable_posteriorReal (W : BrownianSystem Ω) (β : ℝ) :
    Measurable (Function.uncurry (posteriorReal W β)) := by
  exact (continuous_actualParisiFullMagnetization β).measurable.comp
    ((measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)).prodMk
      (J3B.measurable_actualScalar_real W β))

theorem measurable_curvatureReal (W : BrownianSystem Ω) (β : ℝ) :
    Measurable (Function.uncurry (curvatureReal W β)) := by
  exact (continuous_actualParisiFullCurvature β).measurable.comp
    ((measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)).prodMk
      (J3B.measurable_actualScalar_real W β))

theorem posteriorReal_abs_le (W : BrownianSystem Ω) (β s : ℝ) (w : Ω) :
    |posteriorReal W β s w| ≤ 1 :=
  (actualParisiFullMagnetization_curvature_bounds β s.toNNReal _).1

theorem curvatureReal_abs_le (W : BrownianSystem Ω) (β s : ℝ) (w : Ω) :
    |curvatureReal W β s w| ≤ 1 := LJ.actualCurvature_abs_le W β _ w

theorem posteriorReal_continuous_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, Continuous (fun s => posteriorReal W β s w) := by
  filter_upwards [(actualParisiFullScalarDrift β).solution_continuous_ae W] with w hw
  exact (continuous_actualParisiFullMagnetization β).comp
    ((NNReal.continuous_coe.comp continuous_real_toNNReal).prodMk
      (hw.comp continuous_real_toNNReal))

theorem curvatureReal_continuous_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, Continuous (fun s => curvatureReal W β s w) := by
  filter_upwards [LJ.actualCurvature_continuous_ae W β] with w hw
  exact hw.comp continuous_real_toNNReal

theorem curvatureReal_intervalIntegrable (W : BrownianSystem Ω) (β : ℝ)
    (w : Ω) (a b : ℝ) :
    IntervalIntegrable (fun s => curvatureReal W β s w) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    ((measurable_curvatureReal W β).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact ae_of_all _ (fun s => by
    simpa only [Real.norm_eq_abs, abs_one, Function.comp_apply, Function.uncurry_apply_pair,
      id_eq] using curvatureReal_abs_le W β s w)

theorem posterior_pathDrift_intervalIntegrable (W : BrownianSystem Ω) (β : ℝ)
    (w : Ω) (a b : ℝ) :
    IntervalIntegrable (fun s => posteriorReal W β s w *
      (actualParisiFullScalarDrift β).pathDrift W s w) volume a b := by
  let d := actualParisiFullScalarDrift β
  apply (intervalIntegrable_const (c := (d.bound : ℝ))).mono_fun
    (((measurable_posteriorReal W β).mul (d.pathDrift_measurable W)).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  apply ae_of_all
  intro s
  change |posteriorReal W β s w * d.pathDrift W s w| ≤ |(d.bound : ℝ)|
  rw [abs_mul, abs_of_nonneg d.bound.coe_nonneg]
  exact (mul_le_mul (posteriorReal_abs_le W β s w) (d.pathDrift_bound W s w)
    (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

def driftError (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) : ℕ → Ω → ℝ :=
  leftIntegralError (posteriorReal W β) ((actualParisiFullScalarDrift β).pathDrift W) V

def curvatureError (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) : ℕ → Ω → ℝ :=
  leftIntegralError (curvatureReal W β) (fun _ _ => 1) V

theorem driftError_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    J3B.VanishingMeanSquare W.law (driftError W β V) := by
  let := W.isProbability
  exact leftIntegralError_tendsto_L2 W.law (posteriorReal W β)
    ((actualParisiFullScalarDrift β).pathDrift W) (measurable_posteriorReal W β)
    ((actualParisiFullScalarDrift β).pathDrift_measurable W) (posteriorReal_continuous_ae W β)
    1 (actualParisiFullScalarDrift β).bound (NNReal.coe_nonneg _)
    (posteriorReal_abs_le W β) ((actualParisiFullScalarDrift β).pathDrift_bound W) V

theorem curvatureError_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    J3B.VanishingMeanSquare W.law (curvatureError W β V) := by
  let := W.isProbability
  exact leftIntegralError_tendsto_L2 W.law _ _ (measurable_curvatureReal W β)
    measurable_const (curvatureReal_continuous_ae W β) 1 1 zero_le_one
    (curvatureReal_abs_le W β) (by intro s w; norm_num) V

theorem support_driftError_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (l : ℕ) (w : Ω) :
    driftError W β (parisiEquilibriumPhysicalEndpoint β) l w =
      (∑ k ∈ Finset.range (2 ^ l),
        actualParisiFullPosteriorMean W β
          ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k) w *
        (actualParisiFullScalarDrift β).displacement W
          ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l k)
          ((brownianDyadicGrid (parisiEquilibriumPhysicalEndpoint β)).time l (k + 1)) w) -
      ∫ s in (0 : ℝ)..(parisiEquilibriumPhysicalEndpoint β : ℝ),
        cdf (parisiEquilibriumMeasure β : Measure ℝ) (s / β ^ 2) *
          (actualParisiFullPosteriorMean W β s.toNNReal w) ^ 2 := by
  rw [driftError, leftIntegralError_eq _ _ _ _ _
    (fun a b => (actualParisiFullScalarDrift β).pathDrift_integrable W a b w)
    (posterior_pathDrift_intervalIntegrable W β w)]
  simp only [posteriorReal, Real.toNNReal_coe]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (parisiEquilibriumPhysicalEndpoint β).coe_nonneg] at hs
  have hsS : s.toNNReal ≤ parisiEquilibriumPhysicalEndpoint β := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal s hs.1]
    exact hs.2
  change actualParisiFullPosteriorMean W β s.toNNReal w *
    (actualParisiFullScalarDrift β).f s.toNNReal
      (actualParisiFullScalarProcess W β s.toNNReal w) = _
  rw [S32bA.drift_eq_pre β hβ _ hsS _]
  dsimp only [actualParisiFullPosteriorMean]
  rw [Real.coe_toNNReal s hs.1]
  ring

theorem curvatureError_eq (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω) :
    curvatureError W β V l w =
      (∑ k ∈ Finset.range (2 ^ l), LJ.actualCurvature W β
        ((brownianDyadicGrid V).time l k) w * brownianDyadicWidth V l) -
      ∫ s in (0 : ℝ)..V, curvatureReal W β s w := by
  rw [curvatureError, leftIntegralError_eq _ _ _ _ _
    (fun a b => intervalIntegrable_const) (by
      intro a b
      simpa only [mul_one] using curvatureReal_intervalIntegrable W β w a b)]
  simp only [curvatureReal, Real.toNNReal_coe, intervalIntegral.integral_const,
    smul_eq_mul, mul_one, S32bB.dyadic_step_eq_width]

theorem support_rate_integral_eq (W : BrownianSystem Ω) (β : ℝ)
    (w : Ω) :
    (∫ s in (0 : ℝ)..(parisiEquilibriumPhysicalEndpoint β : ℝ),
      J3B.physicalValueRate β s (actualParisiFullScalarProcess W β s.toNNReal w)) =
      -(1 / 2 : ℝ) * ((∫ s in (0 : ℝ)..(parisiEquilibriumPhysicalEndpoint β : ℝ),
        curvatureReal W β s w) +
      ∫ s in (0 : ℝ)..(parisiEquilibriumPhysicalEndpoint β : ℝ),
        cdf (parisiEquilibriumMeasure β : Measure ℝ) (s / β ^ 2) *
          (actualParisiFullPosteriorMean W β s.toNNReal w) ^ 2) := by
  rw [← intervalIntegral.integral_add (curvatureReal_intervalIntegrable W β w _ _)
    (S32bA.posterior_drift_intervalIntegrable W β _ _ w).2,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (parisiEquilibriumPhysicalEndpoint β).coe_nonneg] at hs
  simp only [J3B.physicalValueRate, curvatureReal, LJ.actualCurvature,
    actualParisiFullPosteriorMean, Real.coe_toNNReal s hs.1]
  ring

end SKConstants.Completion.X32B
