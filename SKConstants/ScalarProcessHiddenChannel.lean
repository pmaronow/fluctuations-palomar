module

public import SKConstants.ScalarProcessHistory
public import SKConstants.ScalarProcessSemigroup
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def scalarHiddenSign (b : Bool) : ℝ := if b then 1 else -1

def scalarHiddenWeight (b : Bool) (z : ℝ) : ℝ :=
  if b then scalarPlusWeight z else scalarMinusWeight z

theorem measurable_scalarHiddenWeight (b : Bool) : Measurable (scalarHiddenWeight b) := by
  cases b
  · exact measurable_scalarMinusWeight
  · exact measurable_scalarPlusWeight

theorem scalarHiddenWeight_pos (b : Bool) (z : ℝ) : 0 < scalarHiddenWeight b z := by
  cases b
  · exact scalarMinusWeight_pos z
  · exact scalarPlusWeight_pos z

def scalarHiddenObservationStepKernel (b : Bool) (z : ℝ) (t : ℝ≥0) (n : ℕ) :
    Kernel (ScalarObservationHistory n) ℝ :=
  (gaussianShiftKernel t (scalarHiddenSign b * (t : ℝ))).comap
    (scalarLastField z n) (measurable_scalarLastField z n)

instance scalarHiddenObservationStepKernel_isMarkov (b : Bool) (z : ℝ) (t : ℝ≥0) (n : ℕ) :
    IsMarkovKernel (scalarHiddenObservationStepKernel b z t n) := by
  unfold scalarHiddenObservationStepKernel
  infer_instance

theorem scalarHiddenObservationStepKernel_apply (b : Bool) (z : ℝ) (t : ℝ≥0) (n : ℕ)
    (h : ScalarObservationHistory n) :
    scalarHiddenObservationStepKernel b z t n h =
      gaussianReal (scalarLastField z n h + scalarHiddenSign b * (t : ℝ)) t := rfl

def scalarHiddenObservationHistoryLaw (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → Measure (ScalarObservationHistory n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => scalarHiddenObservationHistoryLaw b z dt n ⊗ₘ
      scalarHiddenObservationStepKernel b z (dt n) n

instance scalarHiddenObservationHistoryLaw_isProbability (b : Bool) (z : ℝ)
    (dt : ℕ → ℝ≥0) (n : ℕ) : IsProbabilityMeasure (scalarHiddenObservationHistoryLaw b z dt n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    change IsProbabilityMeasure (scalarHiddenObservationHistoryLaw b z dt n ⊗ₘ
      scalarHiddenObservationStepKernel b z (dt n) n)
    infer_instance

theorem scalarTransitionKernel_withDensity_hiddenWeight (b : Bool) (z : ℝ) (t : ℝ≥0) :
    (scalarTransitionKernel t z).withDensity
      (fun y => ENNReal.ofReal (scalarHiddenWeight b y)) =
        ENNReal.ofReal (scalarHiddenWeight b z) •
          gaussianReal (z + scalarHiddenSign b * (t : ℝ)) t := by
  by_cases ht : t = 0
  · subst t
    rw [scalarTransitionKernel_zero]
    change (Measure.dirac z).withDensity _ = _
    rw [dirac_withDensity]
    simp only [NNReal.coe_zero, mul_zero, add_zero, gaussianReal_zero_var]
  · have he : scalarTransitionKernel t z = scalarKernelLaw z t := by
      change (if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
      simp only [ht, ↓reduceIte]
    rw [he]
    cases b
    · simpa only [scalarHiddenWeight, scalarHiddenSign, Bool.false_eq_true, ↓reduceIte,
        neg_one_mul, ← sub_eq_add_neg] using scalarKernelLaw_withDensity_minusWeight z t ht
    · simpa only [scalarHiddenWeight, scalarHiddenSign, ↓reduceIte, one_mul] using
        scalarKernelLaw_withDensity_plusWeight z t ht

theorem scalarObservationHistoryLaw_withDensity_hiddenWeight (b : Bool) (z : ℝ)
    (dt : ℕ → ℝ≥0) (n : ℕ) :
    (scalarObservationHistoryLaw z dt n).withDensity
      (fun h => ENNReal.ofReal (scalarHiddenWeight b (scalarLastField z n h))) =
      ENNReal.ofReal (scalarHiddenWeight b z) • scalarHiddenObservationHistoryLaw b z dt n := by
  induction n with
  | zero =>
    change (Measure.dirac PUnit.unit).withDensity (fun _ =>
      ENNReal.ofReal (scalarHiddenWeight b z)) =
      ENNReal.ofReal (scalarHiddenWeight b z) • Measure.dirac PUnit.unit
    exact withDensity_const _
  | succ n ih =>
    change (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n).withDensity
      (fun h : ScalarObservationHistory n × ℝ => ENNReal.ofReal (scalarHiddenWeight b h.2)) =
      ENNReal.ofReal (scalarHiddenWeight b z) •
        (scalarHiddenObservationHistoryLaw b z dt n ⊗ₘ
          scalarHiddenObservationStepKernel b z (dt n) n)
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_withDensity_eq_lintegral_mul _
      (f := fun h : ScalarObservationHistory n × ℝ => ENNReal.ofReal (scalarHiddenWeight b h.2))
      ((measurable_scalarHiddenWeight b).comp measurable_snd).ennreal_ofReal hf]
    simp only [Pi.mul_apply]
    rw [Measure.lintegral_compProd
        (f := fun h : ScalarObservationHistory n × ℝ =>
          ENNReal.ofReal (scalarHiddenWeight b h.2) * f h)
        (((measurable_scalarHiddenWeight b).comp measurable_snd).ennreal_ofReal.mul hf)]
    have hinner : ∀ h : ScalarObservationHistory n,
        (∫⁻ y, ENNReal.ofReal (scalarHiddenWeight b y) * f (h, y)
          ∂scalarObservationStepKernel z (dt n) n h) =
          ENNReal.ofReal (scalarHiddenWeight b (scalarLastField z n h)) *
            (∫⁻ y, f (h, y) ∂scalarHiddenObservationStepKernel b z (dt n) n h) := by
      intro h
      have hi : (∫⁻ y, f (h, y) ∂(scalarTransitionKernel (dt n)
          (scalarLastField z n h)).withDensity (fun y => ENNReal.ofReal (scalarHiddenWeight b y))) =
          ∫⁻ y, ENNReal.ofReal (scalarHiddenWeight b y) * f (h, y)
            ∂scalarTransitionKernel (dt n) (scalarLastField z n h) := by
        simpa only [Pi.mul_apply] using lintegral_withDensity_eq_lintegral_mul _
          (f := fun y => ENNReal.ofReal (scalarHiddenWeight b y))
          (g := fun y => f (h, y))
          (measurable_scalarHiddenWeight b).ennreal_ofReal (hf.comp measurable_prodMk_left)
      rw [scalarObservationStepKernel_apply, ← hi,
        scalarTransitionKernel_withDensity_hiddenWeight, lintegral_smul_measure,
        scalarHiddenObservationStepKernel_apply]
      rfl
    simp_rw [hinner]
    have hmeas : Measurable (fun h : ScalarObservationHistory n =>
        ∫⁻ y, f (h, y) ∂scalarHiddenObservationStepKernel b z (dt n) n h) :=
      hf.lintegral_kernel_prod_right'
    have hi : (∫⁻ h, (∫⁻ y, f (h, y)
        ∂scalarHiddenObservationStepKernel b z (dt n) n h)
        ∂(scalarObservationHistoryLaw z dt n).withDensity
          (fun h => ENNReal.ofReal (scalarHiddenWeight b (scalarLastField z n h)))) =
        ∫⁻ h, ENNReal.ofReal (scalarHiddenWeight b (scalarLastField z n h)) *
          (∫⁻ y, f (h, y) ∂scalarHiddenObservationStepKernel b z (dt n) n h)
          ∂scalarObservationHistoryLaw z dt n := by
      simpa only [Pi.mul_apply] using lintegral_withDensity_eq_lintegral_mul _
        (f := fun h => ENNReal.ofReal (scalarHiddenWeight b (scalarLastField z n h)))
        ((measurable_scalarHiddenWeight b).comp (measurable_scalarLastField z n)).ennreal_ofReal
          hmeas
    rw [← hi, ih, lintegral_smul_measure, lintegral_smul_measure]
    congr 1
    exact (Measure.lintegral_compProd hf).symm

theorem scalarObservationHistoryLaw_eq_hidden_mixture (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    scalarObservationHistoryLaw z dt n =
      ENNReal.ofReal (scalarPlusWeight z) • scalarHiddenObservationHistoryLaw true z dt n +
        ENNReal.ofReal (scalarMinusWeight z) • scalarHiddenObservationHistoryLaw false z dt n := by
  change scalarObservationHistoryLaw z dt n =
    ENNReal.ofReal (scalarHiddenWeight true z) • scalarHiddenObservationHistoryLaw true z dt n +
      ENNReal.ofReal (scalarHiddenWeight false z) • scalarHiddenObservationHistoryLaw false z dt n
  rw [← scalarObservationHistoryLaw_withDensity_hiddenWeight true z dt n,
    ← scalarObservationHistoryLaw_withDensity_hiddenWeight false z dt n,
    ← withDensity_add_left
      (f := fun h => ENNReal.ofReal (scalarHiddenWeight true (scalarLastField z n h)))
      (((measurable_scalarHiddenWeight true).comp (measurable_scalarLastField z n)).ennreal_ofReal)]
  have he : (fun h : ScalarObservationHistory n =>
      ENNReal.ofReal (scalarHiddenWeight true (scalarLastField z n h))) +
      (fun h : ScalarObservationHistory n =>
        ENNReal.ofReal (scalarHiddenWeight false (scalarLastField z n h))) = fun _ => 1 := by
    funext h
    change ENNReal.ofReal (scalarPlusWeight _) + ENNReal.ofReal (scalarMinusWeight _) = 1
    rw [← ENNReal.ofReal_add (scalarPlusWeight_pos _).le (scalarMinusWeight_pos _).le,
      scalarWeight_sum, ENNReal.ofReal_one]
  rw [he, withDensity_const, one_smul]

def scalarHiddenJointHistoryLaw (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Measure (Bool × ScalarObservationHistory n) :=
  ENNReal.ofReal (scalarPlusWeight z) •
    (Measure.dirac true).prod (scalarHiddenObservationHistoryLaw true z dt n) +
  ENNReal.ofReal (scalarMinusWeight z) •
    (Measure.dirac false).prod (scalarHiddenObservationHistoryLaw false z dt n)

instance scalarHiddenJointHistoryLaw_isProbability (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (scalarHiddenJointHistoryLaw z dt n) where
  measure_univ := by
    simp only [scalarHiddenJointHistoryLaw, Measure.add_apply, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (scalarPlusWeight_pos _).le (scalarMinusWeight_pos _).le,
      scalarWeight_sum, ENNReal.ofReal_one]

theorem scalarHiddenJointHistoryLaw_observation_marginal (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (scalarHiddenJointHistoryLaw z dt n).snd = scalarObservationHistoryLaw z dt n := by
  rw [scalarHiddenJointHistoryLaw, Measure.snd_add]
  change (Measure.map Prod.snd
      (ENNReal.ofReal (scalarPlusWeight z) •
        (Measure.dirac true).prod (scalarHiddenObservationHistoryLaw true z dt n))) +
    (Measure.map Prod.snd
      (ENNReal.ofReal (scalarMinusWeight z) •
        (Measure.dirac false).prod (scalarHiddenObservationHistoryLaw false z dt n))) = _
  rw [Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_snd_prod, Measure.map_snd_prod]
  simp only [measure_univ, one_smul]
  exact (scalarObservationHistoryLaw_eq_hidden_mixture z dt n).symm

theorem scalarHiddenJointHistoryLaw_apply_branch (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (A : Set (ScalarObservationHistory n)) :
    scalarHiddenJointHistoryLaw z dt n ({b} ×ˢ A) =
      ENNReal.ofReal (scalarHiddenWeight b z) * scalarHiddenObservationHistoryLaw b z dt n A := by
  cases b <;>
    simp [scalarHiddenJointHistoryLaw, scalarHiddenWeight, Measure.add_apply,
      Measure.smul_apply, Measure.prod_prod, smul_eq_mul]

theorem scalarHiddenJointHistoryLaw_posterior (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (A : Set (ScalarObservationHistory n)) (hA : MeasurableSet A) :
    scalarHiddenJointHistoryLaw z dt n ({b} ×ˢ A) =
      ∫⁻ h in A, ENNReal.ofReal (scalarHiddenWeight b (scalarLastField z n h))
        ∂scalarObservationHistoryLaw z dt n := by
  rw [scalarHiddenJointHistoryLaw_apply_branch]
  have he := congrArg (fun μ : Measure (ScalarObservationHistory n) => μ A)
    (scalarObservationHistoryLaw_withDensity_hiddenWeight b z dt n)
  rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul] at he
  exact he.symm

end SKConstants
