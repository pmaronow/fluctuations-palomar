module

public import SKConstants.Completion.LC1.BrownianPast
public import SKConstants.BrownianContinuousIsometry
public import SKConstants.BrownianDyadicGrid
public import SKConstants.ParisiFullSpinRowMoments

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] BoundedLipschitzDrift.solution
set_option maxHeartbeats 400000
variable {Ω : Type*} [MeasurableSpace Ω]

def rawPastField (b : BoundedLipschitzDrift) (t : ℝ≥0) (p : Iic t → ℝ) : ℝ :=
  scalarForwardPicardPath b t (0, scalarPathFromPast t p) ⟨t, t.coe_nonneg, le_rfl⟩

lemma measurable_rawPastField (b : BoundedLipschitzDrift) (t : ℝ≥0) :
    Measurable (rawPastField b t) :=
  (ContinuousMap.measurable_eval _).comp ((measurable_scalarForwardPicardPath b t).comp
    (measurable_const.prodMk (measurable_scalarPathFromPast t)))

theorem rawPastField_actual (W : BrownianSystem Ω) (b : BoundedLipschitzDrift) :
    ∀ᵐ w ∂W.law, ∀ t : ℝ≥0,
      rawPastField b t (fun s : Iic t => W.B s.1 w) = b.solution W.driver t w := by
  filter_upwards [W.brownian.cont, W.driver_indistinguishable] with w hw hd
  intro t
  let path : ScalarContinuousPath t := scalarContinuousPathRestriction t
    (fun r : ℝ => W.B r.toNNReal w) (hw.comp continuous_real_toNNReal)
  have he : scalarPathFromPast t (fun s : Iic t => W.B s.1 w) = path := by
    change scalarPathFromDenseSamples t _ = path
    convert scalarPathFromDenseSamples_leftInverse t path using 1
    congr 1
    funext k
    dsimp [scalarPathDenseSamples, path, scalarContinuousPathRestriction]
    congr 1
    exact NNReal.coe_injective (Real.coe_toNNReal _ (scalarPathDenseTimes t k).property.1).symm
  unfold rawPastField
  rw [he]
  apply solution_congr_prefix b (scalarContinuousSeedDriver t) W.driver (0, path) w t _ t le_rfl
  intro s hs
  change 0 + path (projIcc 0 (t : ℝ) t.coe_nonneg s) = W.driver s w
  rw [projIcc_of_mem _ ⟨s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩, zero_add]
  dsimp [path, scalarContinuousPathRestriction]
  rw [Real.toNNReal_coe, hd]

def rawPastCurvature (β : ℝ) (t : ℝ≥0) (p : Iic t → ℝ) : ℝ :=
  actualParisiFullCurvature β t (rawPastField (actualParisiFullScalarDrift β) t p)

lemma measurable_rawPastCurvature (β : ℝ) (t : ℝ≥0) :
    Measurable (rawPastCurvature β t) := by
  have hp : Measurable (fun p : Iic t → ℝ =>
      ((t : ℝ), rawPastField (actualParisiFullScalarDrift β) t p)) :=
    (measurable_const : Measurable (fun _ : Iic t → ℝ => (t : ℝ))).prodMk
      (measurable_rawPastField _ t)
  have H := (continuous_actualParisiFullCurvature β).measurable.comp hp
  change Measurable (rawPastCurvature β t) at H
  exact H

lemma rawPastCurvature_abs_le (β : ℝ) (t : ℝ≥0) (p : Iic t → ℝ) :
    |rawPastCurvature β t p| ≤ 1 := actualParisiFullCurvature_abs_le_one β t _

def actualCurvatureProcess (W : BrownianSystem Ω) (β r : ℝ) (w : Ω) : ℝ :=
  actualParisiFullCurvature β r (actualParisiFullScalarProcess W β r.toNNReal w)

lemma measurable_actualCurvatureProcess (W : BrownianSystem Ω) (β : ℝ) :
    Measurable (Function.uncurry (actualCurvatureProcess W β)) := by
  have hy : Measurable (fun q : ℝ × Ω => actualParisiFullScalarProcess W β q.1.toNNReal q.2) := by
    simpa only [zero_add] using LC1.measurable_fullScalar_real_shift W β 0
  have hp : Measurable (fun q : ℝ × Ω => (q.1, actualParisiFullScalarProcess W β q.1.toNNReal q.2)) :=
    measurable_fst.prodMk hy
  have H := (continuous_actualParisiFullCurvature β).measurable.comp hp
  change Measurable (Function.uncurry (actualCurvatureProcess W β)) at H
  exact H

lemma actualCurvatureProcess_abs_le (W : BrownianSystem Ω) (β r : ℝ) (w : Ω) :
    |actualCurvatureProcess W β r w| ≤ 1 := actualParisiFullCurvature_abs_le_one β r _

theorem actualCurvatureProcess_continuous_ae (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, Continuous (fun r : ℝ => actualCurvatureProcess W β r w) := by
  filter_upwards [(actualParisiFullScalarDrift β).solution_continuous_ae W] with w hw
  have hp : Continuous (fun r : ℝ => (r, actualParisiFullScalarProcess W β r.toNNReal w)) :=
    continuous_id.prodMk (hw.comp continuous_real_toNNReal)
  have H := (continuous_actualParisiFullCurvature β).comp hp
  change Continuous (fun r : ℝ => actualCurvatureProcess W β r w) at H
  exact H

theorem rawPastCurvature_actual (W : BrownianSystem Ω) (β : ℝ) :
    ∀ᵐ w ∂W.law, ∀ t : ℝ≥0,
      rawPastCurvature β t (fun s : Iic t => W.B s.1 w) = actualCurvatureProcess W β t w := by
  filter_upwards [rawPastField_actual W (actualParisiFullScalarDrift β)] with w hw
  intro t
  change actualParisiFullCurvature β t (rawPastField _ t _) = _
  rw [hw]
  simp only [actualCurvatureProcess, Real.toNNReal_coe, actualParisiFullScalarProcess]

def curvaturePastCoefficient (β : ℝ) : BrownianContinuousPastCoefficient Unit :=
  fun t u => rawPastCurvature β t u.2

lemma measurable_curvaturePastCoefficient (β : ℝ) (t : ℝ≥0) :
    Measurable (curvaturePastCoefficient β t) := (measurable_rawPastCurvature β t).comp measurable_snd

lemma curvaturePastCoefficient_norm_le (β : ℝ) (t : ℝ≥0) (u : Unit × (Iic t → ℝ)) :
    ‖curvaturePastCoefficient β t u‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, curvaturePastCoefficient] using rawPastCurvature_abs_le β t u.2

end SKConstants.Completion.LBase
