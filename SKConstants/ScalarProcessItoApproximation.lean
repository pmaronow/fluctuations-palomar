module

public import SKConstants.ScalarProcessPosteriorIncrement
public import SKConstants.ScalarProcessInnovation
public import SKConstants.ScalarProcessGenerator
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem scalarDefect_abs_sub_le (y z : ℝ) :
    |scalarDefect y - scalarDefect z| ≤ 2 * |y - z| := by
  have he : scalarDefect y - scalarDefect z =
      -(Real.tanh y - Real.tanh z) * (Real.tanh y + Real.tanh z) := by
    unfold scalarDefect
    ring
  rw [he, abs_mul, abs_neg]
  have hs : |Real.tanh y + Real.tanh z| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [scalar_tanh_abs_le_one y, scalar_tanh_abs_le_one z])
  calc
    _ ≤ |y - z| * 2 := mul_le_mul (scalar_tanh_abs_sub_le y z) hs (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

theorem scalar_tanh_taylor_error (z y : ℝ) :
    |Real.tanh y - Real.tanh z - scalarDefect z * (y - z)| ≤ 2 * (y - z) ^ 2 := by
  let R : ℝ → ℝ := fun w => Real.tanh w - Real.tanh z - scalarDefect z * (w - z)
  have hd (w : ℝ) : HasDerivAt R (scalarDefect w - scalarDefect z) w := by
    convert ((hasDerivAt_tanh_scalar w).sub_const (Real.tanh z)).sub
      (((hasDerivAt_id w).sub_const z).const_mul (scalarDefect z)) using 1
    · funext w
      rfl
    · simp
  have hb : ∀ w ∈ uIcc z y, ‖deriv R w‖ ≤ 2 * |y - z| := by
    intro w hw
    rw [(hd w).deriv, Real.norm_eq_abs]
    exact (scalarDefect_abs_sub_le w z).trans
      (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hw) (by norm_num))
  have h := (convex_uIcc z y).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => (hd w).differentiableAt) hb
    left_mem_uIcc right_mem_uIcc
  have hz : R z = 0 := by simp [R]
  rw [hz, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  change |Real.tanh y - Real.tanh z - scalarDefect z * (y - z)| ≤
    2 * |y - z| * |y - z| at h
  exact h.trans_eq (by nlinarith [sq_abs (y - z)])

def scalarPosteriorItoError (z : ℝ) (t : ℝ≥0) (y : ℝ) : ℝ :=
  scalarPosteriorIncrement z y - scalarDefect z * scalarInnovation z t y

theorem measurable_scalarPosteriorItoError (z : ℝ) (t : ℝ≥0) :
    Measurable (scalarPosteriorItoError z t) := by
  unfold scalarPosteriorItoError
  exact (measurable_scalarPosteriorIncrement z).sub
    ((measurable_id.sub_const z |>.sub_const ((t : ℝ) * Real.tanh z)).const_mul (scalarDefect z))

theorem scalarPosteriorItoError_sq_le (z : ℝ) (t : ℝ≥0) (y : ℝ) :
    (scalarPosteriorItoError z t y) ^ 2 ≤ 8 * (y - z) ^ 4 + 2 * (t : ℝ) ^ 2 := by
  let R := Real.tanh y - Real.tanh z - scalarDefect z * (y - z)
  let D := scalarDefect z * (t : ℝ) * Real.tanh z
  have he : scalarPosteriorItoError z t y = R + D := by
    unfold scalarPosteriorItoError scalarPosteriorIncrement scalarInnovation
    dsimp [R, D]
    ring
  have hr : R ^ 2 ≤ 4 * (y - z) ^ 4 := by
    have h := scalar_tanh_taylor_error z y
    have hn : 0 ≤ 2 * (y - z) ^ 2 := by positivity
    have hs := mul_self_le_mul_self (abs_nonneg R) h
    rw [← pow_two |R|, sq_abs] at hs
    nlinarith
  have hd : D ^ 2 ≤ (t : ℝ) ^ 2 := by
    have ha0 := (scalarDefect_pos z).le
    have ha := scalarDefect_le_one z
    have hm := scalar_tanh_abs_le_one z
    have hasq : (scalarDefect z) ^ 2 ≤ 1 := by nlinarith
    have hmsq : (Real.tanh z) ^ 2 ≤ 1 := (Real.tanh_sq_lt_one z).le
    have hprod := mul_le_mul hasq hmsq (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hfinal := mul_le_mul_of_nonneg_right hprod (sq_nonneg (t : ℝ))
    dsimp [D]
    nlinarith
  rw [he]
  nlinarith [sq_nonneg (R - D)]

theorem integrable_scalarPosteriorItoError (z : ℝ) (t : ℝ≥0) :
    Integrable (scalarPosteriorItoError z t) (scalarTransitionKernel t z) := by
  have hi : Integrable (scalarPosteriorIncrement z) (scalarTransitionKernel t z) := by
    simpa only [pow_one] using integrable_scalarPosteriorIncrement_pow z t 1
  exact hi.sub ((integrable_scalarInnovation_transition z t).const_mul (scalarDefect z))

theorem integral_scalarPosteriorItoError_eq_zero (z : ℝ) (t : ℝ≥0) :
    (∫ y, scalarPosteriorItoError z t y ∂scalarTransitionKernel t z) = 0 := by
  unfold scalarPosteriorItoError
  rw [integral_sub
    (by simpa only [pow_one] using integrable_scalarPosteriorIncrement_pow z t 1)
    ((integrable_scalarInnovation_transition z t).const_mul (scalarDefect z)),
    integral_const_mul, integral_scalarPosteriorIncrement_eq_zero,
    integral_scalarInnovation_transition]
  ring

theorem integrable_scalarPosteriorItoError_sq (z : ℝ) (t : ℝ≥0) :
    Integrable (fun y => scalarPosteriorItoError z t y ^ 2) (scalarTransitionKernel t z) := by
  have hb : Integrable (fun y : ℝ => 8 * (y - z) ^ 4 + 2 * (t : ℝ) ^ 2)
      (scalarTransitionKernel t z) :=
    ((integrable_scalarField_displacement_pow z t 4).const_mul 8).add (integrable_const _)
  exact hb.mono' ((measurable_scalarPosteriorItoError z t).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scalarPosteriorItoError z t y))] using
        scalarPosteriorItoError_sq_le z t y))

theorem integral_scalarPosteriorItoError_sq_le (z : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∫ y, scalarPosteriorItoError z t y ^ 2 ∂scalarTransitionKernel t z) ≤
      82 * (t : ℝ) ^ 2 := by
  have h := integral_mono (integrable_scalarPosteriorItoError_sq z t)
    (((integrable_scalarField_displacement_pow z t 4).const_mul 8).add (integrable_const _))
    (scalarPosteriorItoError_sq_le z t)
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_scalarField_displacement_pow z t 4).const_mul 8)
    (integrable_const _), integral_const_mul, integral_scalarField_displacement_fourth,
    integral_const, probReal_univ, one_smul] at h
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have h3 : (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left htR (sq_nonneg (t : ℝ))]
  have h4 : (t : ℝ) ^ 4 ≤ (t : ℝ) ^ 2 := by
    have hs : (t : ℝ) ^ 2 ≤ 1 := by nlinarith [t.coe_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (t : ℝ))]
  exact h.trans (by nlinarith)

end SKConstants
