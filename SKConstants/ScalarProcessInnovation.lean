module

public import SKConstants.ScalarProcessTail
public import SKConstants.MeshResidualGaussianSquare
public import SKConstants.ScalarProcessGaussianMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKConstants

noncomputable def scalarInnovation (z : ℝ) (t : ℝ≥0) (y : ℝ) : ℝ :=
  y - z - (t : ℝ) * Real.tanh z

theorem scalarKernelLaw_eq_mixture (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    scalarKernelLaw z t =
      ENNReal.ofReal (scalarPlusWeight z) • gaussianReal (z + t) t +
        ENNReal.ofReal (scalarMinusWeight z) • gaussianReal (z - t) t := by
  have he : (fun y ↦ ENNReal.ofReal (scalarKernel z t y)) =
      ENNReal.ofReal (scalarPlusWeight z) • gaussianPDF (z + t) t +
        ENNReal.ofReal (scalarMinusWeight z) • gaussianPDF (z - t) t := by
    funext y
    rw [scalarKernel_eq_mixture z y t ht,
      ENNReal.ofReal_add
        (mul_nonneg (scalarPlusWeight_pos z).le (gaussianPDFReal_nonneg _ _ _))
        (mul_nonneg (scalarMinusWeight_pos z).le (gaussianPDFReal_nonneg _ _ _)),
      ENNReal.ofReal_mul (scalarPlusWeight_pos z).le,
      ENNReal.ofReal_mul (scalarMinusWeight_pos z).le]
    rfl
  rw [scalarKernelLaw, he, withDensity_add_left
    (measurable_gaussianPDF _ _ |>.const_smul _) _,
    withDensity_smul _ (measurable_gaussianPDF _ _),
    withDensity_smul _ (measurable_gaussianPDF _ _),
    ← gaussianReal_of_var_ne_zero _ ht, ← gaussianReal_of_var_ne_zero _ ht]

theorem integrable_scalarKernelLaw_of_gaussian (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0)
    (f : ℝ → ℝ) (hp : Integrable f (gaussianReal (z + t) t))
    (hm : Integrable f (gaussianReal (z - t) t)) : Integrable f (scalarKernelLaw z t) := by
  rw [scalarKernelLaw_eq_mixture z t ht]
  exact (hp.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hm.smul_measure ENNReal.ofReal_ne_top)

theorem integral_scalarKernelLaw_mixture (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0)
    (f : ℝ → ℝ) (hp : Integrable f (gaussianReal (z + t) t))
    (hm : Integrable f (gaussianReal (z - t) t)) :
    ∫ y, f y ∂scalarKernelLaw z t =
      scalarPlusWeight z * (∫ y, f y ∂gaussianReal (z + t) t) +
        scalarMinusWeight z * (∫ y, f y ∂gaussianReal (z - t) t) := by
  rw [scalarKernelLaw_eq_mixture z t ht,
    integral_add_measure (hp.smul_measure ENNReal.ofReal_ne_top)
      (hm.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (scalarPlusWeight_pos z).le,
    ENNReal.toReal_ofReal (scalarMinusWeight_pos z).le]
  rfl

theorem integrable_scalarKernelLaw_id (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    Integrable (fun y ↦ y) (scalarKernelLaw z t) := by
  apply integrable_scalarKernelLaw_of_gaussian z t ht
  · exact (memLp_id_gaussianReal 1).integrable (by simp)
  · exact (memLp_id_gaussianReal 1).integrable (by simp)

theorem integral_id_scalarKernelLaw (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    (∫ y, y ∂scalarKernelLaw z t) = z + (t : ℝ) * Real.tanh z := by
  rw [integral_scalarKernelLaw_mixture z t ht (fun y ↦ y)
    ((memLp_id_gaussianReal 1).integrable (by simp))
    ((memLp_id_gaussianReal 1).integrable (by simp)),
    integral_id_gaussianReal, integral_id_gaussianReal]
  calc
    _ = z * (scalarPlusWeight z + scalarMinusWeight z) +
      (t : ℝ) * (scalarPlusWeight z - scalarMinusWeight z) := by ring
    _ = _ := by rw [scalarWeight_sum, scalarWeight_difference]; ring

theorem integral_scalarInnovation_eq_zero (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∫ y, scalarInnovation z t y ∂scalarKernelLaw z t = 0 := by
  have := scalarKernelLaw_isProbabilityMeasure z t ht
  unfold scalarInnovation
  have hz : Integrable (fun y : ℝ ↦ y - z) (scalarKernelLaw z t) :=
    (integrable_scalarKernelLaw_id z t ht).sub (integrable_const _)
  rw [integral_sub (f := fun y : ℝ ↦ y - z)
      (g := fun _ : ℝ ↦ (t : ℝ) * Real.tanh z) hz (integrable_const _),
    integral_sub (f := fun y : ℝ ↦ y) (g := fun _ : ℝ ↦ z)
      (integrable_scalarKernelLaw_id z t ht) (integrable_const _),
    integral_id_scalarKernelLaw z t ht]
  simp

theorem integrable_scalarInnovation_sq (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    Integrable (fun y ↦ (scalarInnovation z t y) ^ 2) (scalarKernelLaw z t) := by
  have he : (fun y ↦ (scalarInnovation z t y) ^ 2) =
      (fun y ↦ (y - (z + (t : ℝ) * Real.tanh z)) ^ 2) := by
    funext y
    unfold scalarInnovation
    ring
  rw [he]
  exact integrable_scalarKernelLaw_of_gaussian z t ht _
    (gaussianReal_integrable_shift_sq _ _ _) (gaussianReal_integrable_shift_sq _ _ _)

theorem integral_scalarInnovation_sq (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    (∫ y, (scalarInnovation z t y) ^ 2 ∂scalarKernelLaw z t) =
      (t : ℝ) + (t : ℝ) ^ 2 * scalarDefect z := by
  have he : (fun y ↦ (scalarInnovation z t y) ^ 2) =
      (fun y ↦ (y - (z + (t : ℝ) * Real.tanh z)) ^ 2) := by
    funext y
    unfold scalarInnovation
    ring
  rw [he, integral_scalarKernelLaw_mixture z t ht _
    (gaussianReal_integrable_shift_sq _ _ _) (gaussianReal_integrable_shift_sq _ _ _),
    gaussianReal_integral_shift_sq, gaussianReal_integral_shift_sq]
  calc
    _ = (t : ℝ) * (scalarPlusWeight z + scalarMinusWeight z) + (t : ℝ) ^ 2 *
      ((1 + (Real.tanh z) ^ 2) * (scalarPlusWeight z + scalarMinusWeight z) -
        2 * Real.tanh z * (scalarPlusWeight z - scalarMinusWeight z)) := by ring
    _ = _ := by rw [scalarWeight_sum, scalarWeight_difference]; unfold scalarDefect; ring

theorem scalarInnovation_quadratic_error_le (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    |(∫ y, (scalarInnovation z t y) ^ 2 ∂scalarKernelLaw z t) - (t : ℝ)| ≤
      (t : ℝ) ^ 2 := by
  rw [integral_scalarInnovation_sq z t ht, add_sub_cancel_left,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (scalarDefect_pos z).le)]
  exact mul_le_of_le_one_right (sq_nonneg _) (scalarDefect_le_one z)

theorem integrable_scalarInnovation_transition (z : ℝ) (t : ℝ≥0) :
    Integrable (scalarInnovation z t) (scalarTransitionKernel t z) := by
  change Integrable (scalarInnovation z t)
    (if t = 0 then Measure.dirac z else scalarKernelLaw z t)
  by_cases ht : t = 0
  · simp only [ht, ↓reduceIte]
    exact integrable_dirac (by simp)
  · simp only [ht, ↓reduceIte]
    have := scalarKernelLaw_isProbabilityMeasure z t ht
    unfold scalarInnovation
    exact ((integrable_scalarKernelLaw_id z t ht).sub (integrable_const _)).sub
      (integrable_const _)

theorem integrable_scalarInnovation_sq_transition (z : ℝ) (t : ℝ≥0) :
    Integrable (fun y ↦ (scalarInnovation z t y) ^ 2) (scalarTransitionKernel t z) := by
  change Integrable _ (if t = 0 then Measure.dirac z else scalarKernelLaw z t)
  by_cases ht : t = 0
  · simp only [ht, ↓reduceIte]
    exact integrable_dirac (by simp)
  · simp only [ht, ↓reduceIte]
    exact integrable_scalarInnovation_sq z t ht

theorem integral_scalarInnovation_transition (z : ℝ) (t : ℝ≥0) :
    ∫ y, scalarInnovation z t y ∂scalarTransitionKernel t z = 0 := by
  change (∫ y, scalarInnovation z t y
    ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
  by_cases ht : t = 0
  · simp [ht, scalarInnovation]
  · simp only [ht, ↓reduceIte]
    exact integral_scalarInnovation_eq_zero z t ht

theorem integral_scalarInnovation_sq_transition (z : ℝ) (t : ℝ≥0) :
    (∫ y, (scalarInnovation z t y) ^ 2 ∂scalarTransitionKernel t z) =
      (t : ℝ) + (t : ℝ) ^ 2 * scalarDefect z := by
  change (∫ y, (scalarInnovation z t y) ^ 2
    ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
  by_cases ht : t = 0
  · simp [ht, scalarInnovation]
  · simp only [ht, ↓reduceIte]
    exact integral_scalarInnovation_sq z t ht

theorem integral_norm_scalarInnovation_transition (z : ℝ) (t : ℝ≥0) :
    (∫ y, ‖scalarInnovation z t y‖ ∂scalarTransitionKernel t z) ≤
      1 + (t : ℝ) + (t : ℝ) ^ 2 := by
  have hi := integrable_scalarInnovation_transition z t
  have hs := integrable_scalarInnovation_sq_transition z t
  have hh := integral_mono hi.norm ((integrable_const (1 : ℝ)).add hs)
    (fun y ↦ show ‖scalarInnovation z t y‖ ≤ 1 + (scalarInnovation z t y) ^ 2 by
      rw [Real.norm_eq_abs]
      nlinarith [sq_abs (scalarInnovation z t y),
        sq_nonneg (|scalarInnovation z t y| - 1 / 2)])
  rw [integral_add' (integrable_const _) hs, integral_const,
    integral_scalarInnovation_sq_transition] at hh
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hh
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left (scalarDefect_le_one z) (sq_nonneg (t : ℝ))
  nlinarith

end SKConstants
