module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKConstants

lemma gaussianReal_integrable_shift (mu c : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => y - c) (gaussianReal mu v) := by
  exact ((memLp_id_gaussianReal 1).integrable (by simp)).sub (integrable_const c)

lemma gaussianReal_integrable_shift_sq (mu c : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => (y - c) ^ 2) (gaussianReal mu v) := by
  have h : MemLp (fun y : ℝ => y - c) 2 (gaussianReal mu v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const c)
  exact h.integrable_sq

lemma gaussianReal_integral_shift (mu c : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - c) ∂gaussianReal mu v) = mu - c := by
  have hy : Integrable (fun y : ℝ => y) (gaussianReal mu v) :=
    (memLp_id_gaussianReal 1).integrable (by simp)
  rw [integral_sub hy (integrable_const c)]
  simp

lemma gaussianReal_integral_shift_sq (mu c : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - c) ^ 2 ∂gaussianReal mu v) = (v : ℝ) + (mu - c) ^ 2 := by
  have h : MemLp (fun y : ℝ => y - c) 2 (gaussianReal mu v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const c)
  have hvar := variance_eq_sub h
  have hv : variance (fun y : ℝ => y - c) (gaussianReal mu v) = (v : ℝ) := by
    calc
      _ = variance id (gaussianReal mu v) :=
        variance_sub_const (memLp_id_gaussianReal 2).aestronglyMeasurable c
      _ = _ := variance_id_gaussianReal
  rw [hv, gaussianReal_integral_shift] at hvar
  simp only [Pi.pow_apply] at hvar
  linarith

lemma gaussianReal_integral_centered_sq (mu : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - mu) ^ 2 ∂gaussianReal mu v) = (v : ℝ) := by
  simpa using gaussianReal_integral_shift_sq mu mu v

lemma gaussianReal_integral_shift_sq_centered (mu c : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, ((y - c) ^ 2 - ((v : ℝ) + (mu - c) ^ 2))
      ∂gaussianReal mu v) = 0 := by
  rw [integral_sub (gaussianReal_integrable_shift_sq mu c v) (integrable_const _)]
  simp [gaussianReal_integral_shift_sq]

lemma gaussianReal_integrable_shift_sq_centered (mu c : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => (y - c) ^ 2 - ((v : ℝ) + (mu - c) ^ 2))
      (gaussianReal mu v) := by
  exact (gaussianReal_integrable_shift_sq mu c v).sub (integrable_const _)

end SKConstants
