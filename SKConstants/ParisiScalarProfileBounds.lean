module
public import SKConstants.ParisiScalarTerminalCorrection

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
attribute [local irreducible] BoundedLipschitzDrift.solution
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiScalarProfileBounds_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

lemma actualParisiFullCurvatureObservable_integrable (W : BrownianSystem Ω) (β v : ℝ) :
    Integrable (fun w => actualParisiFullCurvature β v
      (actualParisiFullScalarProcess W β v.toNNReal w)) W.law := by
  have HM : Measurable (fun w => actualParisiFullCurvature β v
      (actualParisiFullScalarProcess W β v.toNNReal w)) := by
    have hx := (actualParisiFullScalarDrift β).solution_measurable W v.toNNReal
    change Measurable (actualParisiFullScalarProcess W β v.toNNReal) at hx
    have hp : Measurable (fun w : Ω => (v,actualParisiFullScalarProcess W β v.toNNReal w)) :=
      (measurable_const : Measurable (fun _ : Ω => v)).prodMk hx
    have H := (continuous_actualParisiFullCurvature β).measurable.comp hp
    change Measurable (fun w => actualParisiFullCurvature β v
      (actualParisiFullScalarProcess W β v.toNNReal w)) at H
    exact H
  apply Integrable.of_bound HM.aestronglyMeasurable 1
  exact ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using actualParisiFullCurvature_abs_le_one β v _)

lemma actualParisiFullCurvatureObservable_sq_integrable (W : BrownianSystem Ω) (β v : ℝ) :
    Integrable (fun w => (actualParisiFullCurvature β v
      (actualParisiFullScalarProcess W β v.toNNReal w))^2) W.law := by
  have HM : Measurable (fun w => actualParisiFullCurvature β v
      (actualParisiFullScalarProcess W β v.toNNReal w)) := by
    have hx := (actualParisiFullScalarDrift β).solution_measurable W v.toNNReal
    change Measurable (actualParisiFullScalarProcess W β v.toNNReal) at hx
    have hp : Measurable (fun w : Ω => (v,actualParisiFullScalarProcess W β v.toNNReal w)) :=
      (measurable_const : Measurable (fun _ : Ω => v)).prodMk hx
    have H := (continuous_actualParisiFullCurvature β).measurable.comp hp
    change Measurable (fun w => actualParisiFullCurvature β v
      (actualParisiFullScalarProcess W β v.toNNReal w)) at H
    exact H
  apply Integrable.of_bound (HM.pow_const 2).aestronglyMeasurable 1
  apply ae_of_all
  intro w
  have HP := pow_le_pow_left₀ (abs_nonneg _) (actualParisiFullCurvature_abs_le_one β v
    (actualParisiFullScalarProcess W β v.toNNReal w)) 2
  simpa only [Real.norm_eq_abs,abs_pow,one_pow] using HP

theorem actualParisiFullSusceptibilityExpected_sq_le_squareExpected
    (W : BrownianSystem Ω) (β v : ℝ) :
    (actualParisiFullSusceptibilityExpected W β v)^2≤actualParisiFullSusceptibilitySquareExpected W β v := by
  let A := fun w => actualParisiFullCurvature β v (actualParisiFullScalarProcess W β v.toNNReal w)
  let p := actualParisiFullSusceptibilityExpected W β v
  have hi := actualParisiFullCurvatureObservable_integrable W β v
  have hi2 := actualParisiFullCurvatureObservable_sq_integrable W β v
  change Integrable A W.law at hi
  change Integrable (fun w => (A w)^2) W.law at hi2
  have HV : 0≤∫ w,(A w-p)^2 ∂W.law := integral_nonneg (fun _ => sq_nonneg _)
  have HE : (fun w => (A w-p)^2)=fun w => (A w)^2-(2*p)*A w+p^2 := by funext w;ring
  have his := hi2.sub (hi.const_mul (2*p))
  change Integrable (fun w => (A w)^2-(2*p)*A w) W.law at his
  rw [HE,integral_add his (integrable_const _),
    integral_sub hi2 (hi.const_mul _),integral_const_mul,integral_const,probReal_univ,one_smul] at HV
  have HP : (∫ w,A w ∂W.law)=p := rfl
  rw [HP] at HV
  change p^2≤∫ w,(A w)^2 ∂W.law
  nlinarith

theorem actualParisiFullSusceptibilitySquareExpected_bounds (W : BrownianSystem Ω) (β v : ℝ) :
    actualParisiFullSusceptibilitySquareExpected W β v∈Icc (0:ℝ) 1 := by
  unfold actualParisiFullSusceptibilitySquareExpected
  refine ⟨integral_nonneg (fun _ => sq_nonneg _),?_⟩
  have H := integral_mono (actualParisiFullCurvatureObservable_sq_integrable W β v) (integrable_const (1:ℝ))
    (fun w => by
      have HP := pow_le_pow_left₀ (abs_nonneg _) (actualParisiFullCurvature_abs_le_one β v
        (actualParisiFullScalarProcess W β v.toNNReal w)) 2
      simpa only [sq_abs,one_pow] using HP)
  simpa only [integral_const,probReal_univ,one_smul] using H

theorem actualParisiFullEntropyRateExpected_bounds (W : BrownianSystem Ω) (β v : ℝ) :
    actualParisiFullEntropyRateExpected W β v∈Icc (0:ℝ) 1 := by
  let g := fun x => (actualParisiFullCurvature β v x)^2/(1-(actualParisiFullMagnetization β v x)^2)
  have hpair : Continuous (fun x : ℝ => (v,x)) := continuous_const.prodMk continuous_id
  have ha := (continuous_actualParisiFullCurvature β).comp hpair
  have hm := (continuous_actualParisiFullMagnetization β).comp hpair
  change Continuous (actualParisiFullCurvature β v) at ha
  change Continuous (actualParisiFullMagnetization β v) at hm
  have hg : Continuous g := by
    apply (ha.pow 2).div (continuous_const.sub (hm.pow 2))
    intro x
    change 1-(actualParisiFullMagnetization β v x)^2≠0
    have HS := actualParisiFullMagnetization_strict_bounds β v x
    nlinarith
  have hx := (actualParisiFullScalarDrift β).solution_measurable W v.toNNReal
  change Measurable (actualParisiFullScalarProcess W β v.toNNReal) at hx
  have HM := hg.measurable.comp hx
  change Measurable (fun w => g (actualParisiFullScalarProcess W β v.toNNReal w)) at HM
  have hi : Integrable (fun w => g (actualParisiFullScalarProcess W β v.toNNReal w)) W.law :=
    Integrable.of_bound HM.aestronglyMeasurable 1
      (ae_of_all _ (fun w => by
        have H := actualParisiFullEntropyRate_bounds β v (actualParisiFullScalarProcess W β v.toNNReal w)
        dsimp only [g]
        simpa only [Real.norm_eq_abs,abs_of_nonneg H.1] using H.2))
  unfold actualParisiFullEntropyRateExpected
  refine ⟨integral_nonneg (fun w => (actualParisiFullEntropyRate_bounds β v _).1),?_⟩
  have H := integral_mono hi (integrable_const (1:ℝ))
    (fun w => (actualParisiFullEntropyRate_bounds β v _).2)
  simpa only [integral_const,probReal_univ,one_smul] using H

end SKConstants
