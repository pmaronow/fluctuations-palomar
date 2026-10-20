module
public import SKConstants.ScalarProcessContinuous
public import SKConstants.ScalarProcessSampledHistory
public import SKConstants.ScalarProcessSeed
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma scalarLastField_one_hasLaw (z : ℝ) (dt : ℕ → ℝ≥0) :
    HasLaw (scalarLastField z 1) (scalarTransitionKernel (dt 0) z)
      (scalarObservationHistoryLaw z dt 1) := by
  let : IsMarkovKernel (scalarObservationStepKernel z (dt 0) 0) :=
    scalarObservationStepKernel_isMarkov z (dt 0) 0
  refine ⟨(measurable_scalarLastField z 1).aemeasurable, ?_⟩
  change (Measure.dirac PUnit.unit ⊗ₘ scalarObservationStepKernel z (dt 0) 0).map Prod.snd = _
  ext A hA
  rw [Measure.map_apply measurable_snd hA, Measure.dirac_compProd_apply (measurable_snd hA)]
  change (scalarTransitionKernel (dt 0) z) ((Prod.mk PUnit.unit) ⁻¹' (Prod.snd ⁻¹' A)) = _
  rfl

lemma scalarHiddenContinuousField_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (T : ℝ≥0) :
    HasLaw (scalarHiddenContinuousField z B T) (scalarTransitionKernel T z)
      (scalarHiddenBrownianLaw z P) := by
  let t : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * T
  have ht : Monotone t := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)
  have ht0 : t 0 = 0 := by simp [t]
  have hdt : brownianMeshVariance t 0 = T := by simp [brownianMeshVariance, t]
  have hH := scalarBrownianPriorField_history_hasLaw hB z t ht ht0 1
  have h := (scalarLastField_one_hasLaw z (brownianMeshVariance t)).fun_comp hH
  rw [hdt] at h
  convert h using 1
  · funext u
    simp only [scalarLastField, scalarSampledFieldHistory, t, Nat.zero_add, Nat.cast_one, one_mul,
      scalarHiddenContinuousField]
  · unfold scalarHiddenBrownianLaw scalarHiddenPriorBool
    rfl

lemma integral_scalarHiddenContinuousField_comp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (T : ℝ≥0) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ u, f (scalarHiddenContinuousField z B T u) ∂scalarHiddenBrownianLaw z P) =
      ∫ y, f y ∂scalarTransitionKernel T z :=
  (scalarHiddenContinuousField_hasLaw hB z T).integral_comp hf.aestronglyMeasurable

lemma integral_scalarHiddenContinuousField_defect {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (T : ℝ≥0) :
    (∫ u, scalarDefect (scalarHiddenContinuousField z B T u) ∂scalarHiddenBrownianLaw z P) =
      if T = 0 then scalarDefect z else scalarP z T := by
  rw [integral_scalarHiddenContinuousField_comp hB z T scalarDefect measurable_scalarDefect]
  by_cases ht : T = 0
  · subst T
    rw [scalarTransitionKernel_zero]
    simp only [Kernel.id_apply, integral_dirac, ite_true]
  · simp only [ht, ite_false]
    have he : scalarTransitionKernel T z = scalarKernelLaw z T := by
      change (if T = 0 then Measure.dirac z else scalarKernelLaw z T) = _
      simp only [ht, ite_false]
    rw [he]
    change (∫ y, scalarDefect y ∂scalarKernelLaw z T) = scalarP z T
    rfl

lemma integral_scalarHiddenContinuousField_defect_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (T : ℝ≥0) :
    (∫ u, (scalarDefect (scalarHiddenContinuousField z B T u)) ^ 2 ∂scalarHiddenBrownianLaw z P) =
      if T = 0 then (scalarDefect z) ^ 2 else scalarR z T := by
  rw [integral_scalarHiddenContinuousField_comp hB z T (fun y => (scalarDefect y) ^ 2)
    (measurable_scalarDefect.pow_const 2)]
  by_cases ht : T = 0
  · subst T
    rw [scalarTransitionKernel_zero]
    simp only [Kernel.id_apply, integral_dirac, ite_true]
  · simp only [ht, ite_false]
    have he : scalarTransitionKernel T z = scalarKernelLaw z T := by
      change (if T = 0 then Measure.dirac z else scalarKernelLaw z T) = _
      simp only [ht, ite_false]
    rw [he]
    change (∫ y, (scalarDefect y) ^ 2 ∂scalarKernelLaw z T) = scalarR z T
    rfl

lemma integral_scalarHiddenContinuousField_defect_le_sharp_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (T : ℝ≥0) (hT : T ≠ 0) :
    (∫ u, scalarDefect (scalarHiddenContinuousField z B T u) ∂scalarHiddenBrownianLaw z P) ≤
      4 * (Real.exp (-(T : ℝ) / 2) / Real.cosh z) *
        (Real.sqrt (2 * Real.pi * (T : ℝ)))⁻¹ := by
  rw [integral_scalarHiddenContinuousField_defect hB z T, ite_eq_right hT]
  exact scalarP_le_sharp_tail z T

lemma integral_scalarHiddenContinuousField_defect_sq_ge_compact_tailScale {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (z R : ℝ) (T : ℝ≥0)
    (hT : 1 ≤ (T : ℝ)) (hR : 0 ≤ R) (hz : |z| ≤ R) :
    scalarCompactTailConstant R * scalarTailScale T ≤
      (∫ u, (scalarDefect (scalarHiddenContinuousField z B T u)) ^ 2 ∂scalarHiddenBrownianLaw z P) := by
  have ht0 : T ≠ 0 := by
    intro he
    simp only [he, NNReal.coe_zero] at hT
    linarith
  rw [integral_scalarHiddenContinuousField_defect_sq hB z T, ite_eq_right ht0]
  exact scalarR_ge_compact_tailScale z R T hT hR hz

end SKConstants
