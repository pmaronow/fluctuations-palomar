module
public import SKConstants.ScalarProcessGenerator
public import SKConstants.ScalarProcessPosteriorIncrement
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

public section
noncomputable section
namespace SKConstants
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

@[expose] def scalarLogCosh (y : ℝ) : ℝ := Real.log (Real.cosh y)

theorem hasDerivAt_scalarLogCosh (y : ℝ) : HasDerivAt scalarLogCosh (Real.tanh y) y := by
  change HasDerivAt (fun x => Real.log (Real.cosh x)) (Real.tanh y) y
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'

theorem deriv_scalarLogCosh : deriv scalarLogCosh = Real.tanh :=
  funext fun y => (hasDerivAt_scalarLogCosh y).deriv

theorem deriv_deriv_scalarLogCosh : deriv (deriv scalarLogCosh) = scalarDefect := by
  rw [deriv_scalarLogCosh]
  exact funext fun y => (hasDerivAt_tanh_scalar y).deriv

theorem contDiff_scalarLogCosh (n : ℕ) : ContDiff ℝ n scalarLogCosh :=
  Real.contDiff_cosh.log (fun y => (Real.cosh_pos y).ne')

theorem iteratedDeriv_scalarLogCosh_zero (y : ℝ) :
    iteratedDeriv 0 scalarLogCosh y = scalarLogCosh y := rfl

theorem iteratedDeriv_scalarLogCosh_one (y : ℝ) :
    iteratedDeriv 1 scalarLogCosh y = Real.tanh y := by
  rw [iteratedDeriv_eq_iterate]
  exact congrFun deriv_scalarLogCosh y

theorem iteratedDeriv_scalarLogCosh_two (y : ℝ) :
    iteratedDeriv 2 scalarLogCosh y = scalarDefect y := by
  rw [iteratedDeriv_eq_iterate]
  exact congrFun deriv_deriv_scalarLogCosh y

theorem iteratedDeriv_scalarLogCosh_three (y : ℝ) :
    iteratedDeriv 3 scalarLogCosh y = -2 * Real.tanh y * scalarDefect y := by
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (deriv scalarLogCosh)) y = _
  rw [deriv_deriv_scalarLogCosh]
  exact (hasDerivAt_scalarDefect y).deriv

theorem scalarLogCosh_third_derivative_abs_le (y : ℝ) :
    |iteratedDeriv 3 scalarLogCosh y| ≤ 2 := by
  rw [iteratedDeriv_scalarLogCosh_three, abs_mul, abs_mul,
    abs_of_pos (scalarDefect_pos y)]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h1 := scalar_tanh_abs_le_one y
  have h2 := scalarDefect_le_one y
  have h3 := mul_le_mul_of_nonneg_left h1 (scalarDefect_pos y).le
  nlinarith [abs_nonneg (Real.tanh y)]

theorem scalarLogCosh_taylorWithinEval_one (z y : ℝ) (hzy : z ≠ y) :
    taylorWithinEval scalarLogCosh 1 (uIcc z y) z y =
      scalarLogCosh z + Real.tanh z * (y - z) := by
  have hw (k : ℕ) : iteratedDerivWithin k scalarLogCosh (uIcc z y) z =
      iteratedDeriv k scalarLogCosh z :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hzy)
      (contDiff_scalarLogCosh k).contDiffAt (left_mem_uIcc)
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hw 0, hw 1]
  norm_num [iteratedDeriv_scalarLogCosh_zero, iteratedDeriv_scalarLogCosh_one]
  ring

theorem scalarLogCosh_taylorWithinEval_two (z y : ℝ) (hzy : z ≠ y) :
    taylorWithinEval scalarLogCosh 2 (uIcc z y) z y =
      scalarLogCosh z + Real.tanh z * (y - z) + scalarDefect z * (y - z) ^ 2 / 2 := by
  have hw (k : ℕ) : iteratedDerivWithin k scalarLogCosh (uIcc z y) z =
      iteratedDeriv k scalarLogCosh z :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hzy)
      (contDiff_scalarLogCosh k).contDiffAt (left_mem_uIcc)
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hw 0, hw 1, hw 2]
  norm_num [iteratedDeriv_scalarLogCosh_zero, iteratedDeriv_scalarLogCosh_one,
    iteratedDeriv_scalarLogCosh_two]
  ring

theorem scalarLogCosh_taylor_one_abs_le (z y : ℝ) :
    |scalarLogCosh y - scalarLogCosh z - Real.tanh z * (y - z)| ≤ (y - z) ^ 2 / 2 := by
  by_cases hzy : z = y
  · subst y
    simp
  obtain ⟨u, _, hu⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := scalarLogCosh) (n := 1) hzy (contDiff_scalarLogCosh 2).contDiffOn
  rw [scalarLogCosh_taylorWithinEval_one z y hzy, iteratedDeriv_scalarLogCosh_two] at hu
  have heq : scalarLogCosh y - scalarLogCosh z - Real.tanh z * (y - z) =
      scalarDefect u * (y - z) ^ 2 / 2 := by
    norm_num at hu
    linarith
  rw [heq, abs_of_nonneg (div_nonneg
    (mul_nonneg (scalarDefect_pos u).le (sq_nonneg _)) (by norm_num))]
  have hh := mul_le_mul_of_nonneg_right (scalarDefect_le_one u) (sq_nonneg (y - z))
  linarith

@[expose] def scalarLogCoshTaylorResidual (z y : ℝ) : ℝ :=
  scalarLogCosh y - scalarLogCosh z - Real.tanh z * (y - z) -
    scalarDefect z * (y - z) ^ 2 / ((2 : ℕ) : ℝ)

theorem scalarLogCosh_taylor_two_abs_le (z y : ℝ) :
    |scalarLogCoshTaylorResidual z y| ≤ |y - z| ^ 3 / 3 := by
  by_cases hzy : z = y
  · subst y
    simp [scalarLogCoshTaylorResidual]
  obtain ⟨u, _, hu⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := scalarLogCosh) (n := 2) hzy (contDiff_scalarLogCosh 3).contDiffOn
  rw [scalarLogCosh_taylorWithinEval_two z y hzy] at hu
  have heq : scalarLogCoshTaylorResidual z y =
      iteratedDeriv 3 scalarLogCosh u * (y - z) ^ 3 / 6 := by
    dsimp [scalarLogCoshTaylorResidual]
    norm_num at hu
    linarith
  rw [heq, abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
  have hh := mul_le_mul_of_nonneg_right (scalarLogCosh_third_derivative_abs_le u)
    (pow_nonneg (abs_nonneg (y - z)) 3)
  linarith

@[expose] def scalarLogCoshItoError (z : ℝ) (t : ℝ≥0) (y : ℝ) : ℝ :=
  scalarLogCosh y - scalarLogCosh z - (t : ℝ) / ((2 : ℕ) : ℝ) -
    (t : ℝ) * Real.tanh z ^ 2 / ((2 : ℕ) : ℝ) - Real.tanh z * scalarInnovation z t y

theorem scalarLogCoshItoError_eq_taylor (z : ℝ) (t : ℝ≥0) (y : ℝ) :
    scalarLogCoshItoError z t y = scalarLogCoshTaylorResidual z y +
      scalarDefect z * ((y - z) ^ 2 - (t : ℝ)) / 2 := by
  dsimp [scalarLogCoshItoError, scalarLogCoshTaylorResidual, scalarInnovation, scalarDefect]
  ring

theorem scalarLogCoshItoError_abs_le (z : ℝ) (t : ℝ≥0) (y : ℝ) :
    |scalarLogCoshItoError z t y| ≤ (y - z) ^ 2 / 2 + (t : ℝ) / 2 := by
  have he : scalarLogCoshItoError z t y =
      (scalarLogCosh y - scalarLogCosh z - Real.tanh z * (y - z)) - (t : ℝ) * scalarDefect z / 2 := by
    dsimp [scalarLogCoshItoError, scalarInnovation, scalarDefect]
    ring
  rw [he]
  have hh := abs_sub (scalarLogCosh y - scalarLogCosh z - Real.tanh z * (y - z))
    ((t : ℝ) * scalarDefect z / 2)
  have hd : |(t : ℝ) * scalarDefect z / 2| ≤ (t : ℝ) / 2 := by
    rw [abs_of_nonneg (div_nonneg
      (mul_nonneg t.coe_nonneg (scalarDefect_pos z).le) (by norm_num))]
    have hm := mul_le_mul_of_nonneg_left (scalarDefect_le_one z) t.coe_nonneg
    linarith
  exact hh.trans (by linarith [scalarLogCosh_taylor_one_abs_le z y])

@[fun_prop] theorem continuous_scalarLogCosh : Continuous scalarLogCosh :=
  (contDiff_scalarLogCosh 0).continuous

theorem continuous_scalarLogCoshItoError_uncurry (t : ℝ≥0) :
    Continuous (fun zy : ℝ × ℝ => scalarLogCoshItoError zy.1 t zy.2) := by
  dsimp [scalarLogCoshItoError, scalarInnovation]
  have hc : Continuous Real.tanh := scalar_tanh_lipschitz.continuous
  fun_prop

theorem measurable_scalarLogCoshItoError (z : ℝ) (t : ℝ≥0) :
    Measurable (scalarLogCoshItoError z t) :=
  ((continuous_scalarLogCoshItoError_uncurry t).comp
    (continuous_const.prodMk continuous_id)).measurable

theorem scalarLogCoshItoError_sq_le (z : ℝ) (t : ℝ≥0) (y : ℝ) :
    scalarLogCoshItoError z t y ^ 2 ≤ (y - z) ^ 4 / 2 + (t : ℝ) ^ 2 / 2 := by
  have hh := (sq_le_sq₀ (abs_nonneg (scalarLogCoshItoError z t y))
    (show 0 ≤ (y - z) ^ 2 / 2 + (t : ℝ) / 2 by positivity)).2
    (scalarLogCoshItoError_abs_le z t y)
  rw [sq_abs] at hh
  nlinarith [sq_nonneg ((y - z) ^ 2 - (t : ℝ))]

theorem integrable_scalarLogCoshItoError (z : ℝ) (t : ℝ≥0) :
    Integrable (scalarLogCoshItoError z t) (scalarTransitionKernel t z) := by
  have hb := ((integrable_scalarField_displacement_pow z t 2).div_const 2).add
    (integrable_const ((t : ℝ) / 2))
  apply hb.mono' (measurable_scalarLogCoshItoError z t).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    simpa only [Real.norm_eq_abs, Pi.add_apply] using scalarLogCoshItoError_abs_le z t y

theorem integrable_scalarLogCoshItoError_sq (z : ℝ) (t : ℝ≥0) :
    Integrable (fun y => scalarLogCoshItoError z t y ^ 2) (scalarTransitionKernel t z) := by
  have hb := ((integrable_scalarField_displacement_pow z t 4).div_const 2).add
    (integrable_const ((t : ℝ) ^ 2 / 2))
  apply hb.mono' ((measurable_scalarLogCoshItoError z t).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scalarLogCoshItoError z t y)), Pi.add_apply] using
      scalarLogCoshItoError_sq_le z t y

theorem integral_scalarLogCoshItoError_sq_le (z : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∫ y, scalarLogCoshItoError z t y ^ 2 ∂scalarTransitionKernel t z) ≤ 6 * (t : ℝ) ^ 2 := by
  have hi4 := integrable_scalarField_displacement_pow z t 4
  have hb := (hi4.div_const 2).add (integrable_const ((t : ℝ) ^ 2 / 2))
  have hh := integral_mono (integrable_scalarLogCoshItoError_sq z t) hb
    (scalarLogCoshItoError_sq_le z t)
  have he : (∫ y, ((y - z) ^ 4 / 2 + (t : ℝ) ^ 2 / 2) ∂scalarTransitionKernel t z) =
      (∫ y, (y - z) ^ 4 ∂scalarTransitionKernel t z) / 2 + (t : ℝ) ^ 2 / 2 := by
    rw [integral_add (hi4.div_const 2) (integrable_const _), integral_div]
    simp
  change (∫ y, scalarLogCoshItoError z t y ^ 2 ∂scalarTransitionKernel t z) ≤
    (∫ y, ((y - z) ^ 4 / 2 + (t : ℝ) ^ 2 / 2) ∂scalarTransitionKernel t z) at hh
  rw [he] at hh
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have h3 : (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left htR (sq_nonneg (t : ℝ))]
  have h4 : (t : ℝ) ^ 4 ≤ (t : ℝ) ^ 2 := by
    have h2 : (t : ℝ) ^ 2 ≤ 1 := by nlinarith [t.coe_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (t : ℝ))]
  rw [integral_scalarField_displacement_fourth] at hh
  nlinarith

theorem integrable_scalarField_displacement_abs_cube (z : ℝ) (t : ℝ≥0) :
    Integrable (fun y : ℝ => |y - z| ^ 3) (scalarTransitionKernel t z) := by
  have hh := (integrable_scalarField_displacement_pow z t 3).norm
  simpa only [Real.norm_eq_abs, abs_pow] using hh

theorem integral_scalarField_displacement_abs_cube_le (z : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∫ y : ℝ, |y - z| ^ 3 ∂scalarTransitionKernel t z) ≤
      6 * (t : ℝ) * Real.sqrt (t : ℝ) := by
  by_cases ht0 : t = 0
  · subst t
    rw [scalarTransitionKernel_zero, Kernel.id_apply]
    simp
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht0)
  let s := Real.sqrt (t : ℝ)
  have hspos : 0 < s := Real.sqrt_pos.mpr htpos
  have hs2 : s ^ 2 = (t : ℝ) := Real.sq_sqrt t.coe_nonneg
  have hpoint (y : ℝ) : |y - z| ^ 3 ≤ (s * (y - z) ^ 2 + (y - z) ^ 4 / s) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (mul_le_mul_iff_right₀ hspos).mp
    have habs2 : |y - z| ^ 2 = (y - z) ^ 2 := sq_abs _
    have habs4 : |y - z| ^ 4 = (y - z) ^ 4 := by simp only [Even.pow_abs (by decide : Even 4)]
    have hdiv : ((y - z) ^ 4 / s) * s = (y - z) ^ 4 := div_mul_cancel₀ _ hspos.ne'
    nlinarith [mul_nonneg (sq_nonneg (|y - z|)) (sq_nonneg (|y - z| - s))]
  have hi2 := integrable_scalarField_displacement_pow z t 2
  have hi4 := integrable_scalarField_displacement_pow z t 4
  have hb := ((hi2.const_mul s).add (hi4.div_const s)).div_const 2
  have hh := integral_mono (integrable_scalarField_displacement_abs_cube z t) hb hpoint
  have he : (∫ y : ℝ, (s * (y - z) ^ 2 + (y - z) ^ 4 / s) / 2 ∂scalarTransitionKernel t z) =
      (s * ((t : ℝ) + (t : ℝ) ^ 2) +
        (3 * (t : ℝ) ^ 2 + 6 * (t : ℝ) ^ 3 + (t : ℝ) ^ 4) / s) / 2 := by
    rw [integral_div, integral_add (hi2.const_mul s) (hi4.div_const s),
      integral_const_mul, integral_div, integral_scalarField_displacement_sq,
      integral_scalarField_displacement_fourth]
  change (∫ y : ℝ, |y - z| ^ 3 ∂scalarTransitionKernel t z) ≤
    (∫ y : ℝ, (s * (y - z) ^ 2 + (y - z) ^ 4 / s) / 2 ∂scalarTransitionKernel t z) at hh
  rw [he] at hh
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have h3 : (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left htR (sq_nonneg (t : ℝ))]
  have h4 : (t : ℝ) ^ 4 ≤ (t : ℝ) ^ 2 := by
    have h2 : (t : ℝ) ^ 2 ≤ 1 := by nlinarith [t.coe_nonneg]
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (t : ℝ))]
  have hbnd : (s * ((t : ℝ) + (t : ℝ) ^ 2) +
      (3 * (t : ℝ) ^ 2 + 6 * (t : ℝ) ^ 3 + (t : ℝ) ^ 4) / s) / 2 ≤ 6 * (t : ℝ) * s := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (mul_le_mul_iff_right₀ hspos).mp
    have hdiv : ((3 * (t : ℝ) ^ 2 + 6 * (t : ℝ) ^ 3 + (t : ℝ) ^ 4) / s) * s =
        3 * (t : ℝ) ^ 2 + 6 * (t : ℝ) ^ 3 + (t : ℝ) ^ 4 := div_mul_cancel₀ _ hspos.ne'
    nlinarith [mul_le_mul_of_nonneg_left htR t.coe_nonneg]
  exact hh.trans hbnd

theorem measurable_scalarLogCoshTaylorResidual (z : ℝ) :
    Measurable (scalarLogCoshTaylorResidual z) := by
  apply Continuous.measurable
  change Continuous (fun y => scalarLogCoshTaylorResidual z y)
  dsimp [scalarLogCoshTaylorResidual]
  fun_prop

theorem integrable_scalarLogCoshTaylorResidual (z : ℝ) (t : ℝ≥0) :
    Integrable (scalarLogCoshTaylorResidual z) (scalarTransitionKernel t z) := by
  apply ((integrable_scalarField_displacement_abs_cube z t).div_const 3).mono'
    (measurable_scalarLogCoshTaylorResidual z).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    simpa only [Real.norm_eq_abs] using scalarLogCosh_taylor_two_abs_le z y

theorem integral_scalarLogCoshItoError_eq (z : ℝ) (t : ℝ≥0) :
    (∫ y, scalarLogCoshItoError z t y ∂scalarTransitionKernel t z) =
      (∫ y, scalarLogCoshTaylorResidual z y ∂scalarTransitionKernel t z) +
        scalarDefect z * (t : ℝ) ^ 2 / 2 := by
  have hi2 := integrable_scalarField_displacement_pow z t 2
  have he : scalarLogCoshItoError z t = fun y => scalarLogCoshTaylorResidual z y +
      (scalarDefect z / 2) * ((y - z) ^ 2 - (t : ℝ)) := by
    funext y
    rw [scalarLogCoshItoError_eq_taylor]
    ring
  have hiq : Integrable (fun y => (scalarDefect z / 2) * ((y - z) ^ 2 - (t : ℝ)))
      (scalarTransitionKernel t z) := by
    simpa only [Pi.sub_apply] using (hi2.sub (integrable_const (t : ℝ))).const_mul (scalarDefect z / 2)
  rw [he]
  change (∫ y, (scalarLogCoshTaylorResidual z y +
    (scalarDefect z / 2) * ((y - z) ^ 2 - (t : ℝ))) ∂scalarTransitionKernel t z) = _
  rw [integral_add (integrable_scalarLogCoshTaylorResidual z t) hiq,
    integral_const_mul, integral_sub hi2 (integrable_const _), integral_scalarField_displacement_sq]
  simp
  ring

theorem integral_scalarLogCoshItoError_abs_le (z : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    |∫ y, scalarLogCoshItoError z t y ∂scalarTransitionKernel t z| ≤
      3 * (t : ℝ) * Real.sqrt (t : ℝ) := by
  have hiR := integrable_scalarLogCoshTaylorResidual z t
  have hi3 := integrable_scalarField_displacement_abs_cube z t
  have hR : |∫ y, scalarLogCoshTaylorResidual z y ∂scalarTransitionKernel t z| ≤
      2 * (t : ℝ) * Real.sqrt (t : ℝ) := by
    have hh := integral_mono hiR.norm (hi3.div_const 3) fun y => by
      simpa only [Real.norm_eq_abs] using scalarLogCosh_taylor_two_abs_le z y
    have hnorm := norm_integral_le_integral_norm (f := scalarLogCoshTaylorResidual z)
      (μ := scalarTransitionKernel t z)
    have he : (∫ y, |y - z| ^ 3 / 3 ∂scalarTransitionKernel t z) =
        (∫ y, |y - z| ^ 3 ∂scalarTransitionKernel t z) / 3 := by rw [integral_div]
    change (∫ y, ‖scalarLogCoshTaylorResidual z y‖ ∂scalarTransitionKernel t z) ≤
      (∫ y, |y - z| ^ 3 / 3 ∂scalarTransitionKernel t z) at hh
    rw [he] at hh
    rw [Real.norm_eq_abs] at hnorm
    linarith [integral_scalarField_displacement_abs_cube_le z t ht]
  rw [integral_scalarLogCoshItoError_eq]
  have hh := abs_add_le (∫ y, scalarLogCoshTaylorResidual z y ∂scalarTransitionKernel t z)
    (scalarDefect z * (t : ℝ) ^ 2 / 2)
  have hdef : |scalarDefect z * (t : ℝ) ^ 2 / 2| ≤ (t : ℝ) ^ 2 / 2 := by
    rw [abs_of_nonneg (div_nonneg
      (mul_nonneg (scalarDefect_pos z).le (sq_nonneg _)) (by norm_num))]
    have hd := mul_le_mul_of_nonneg_right (scalarDefect_le_one z) (sq_nonneg (t : ℝ))
    linarith
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have hs0 := Real.sqrt_nonneg (t : ℝ)
  have hs2 := Real.sq_sqrt t.coe_nonneg
  have hts : (t : ℝ) ≤ Real.sqrt (t : ℝ) := by
    nlinarith [t.coe_nonneg]
  have hmul := mul_le_mul_of_nonneg_left hts t.coe_nonneg
  nlinarith

@[expose] def scalarLogCoshBias (t : ℝ≥0) (z : ℝ) : ℝ :=
  ∫ y, scalarLogCoshItoError z t y ∂scalarTransitionKernel t z

theorem measurable_scalarLogCoshBias (t : ℝ≥0) : Measurable (scalarLogCoshBias t) := by
  have hh := (continuous_scalarLogCoshItoError_uncurry t).measurable.stronglyMeasurable
    |>.integral_kernel_prod_right' (κ := scalarTransitionKernel t)
  exact hh.measurable

@[expose] def scalarCenteredLogCoshItoError (z : ℝ) (t : ℝ≥0) (y : ℝ) : ℝ :=
  scalarLogCoshItoError z t y - scalarLogCoshBias t z

theorem measurable_scalarCenteredLogCoshItoError_uncurry (t : ℝ≥0) :
    Measurable (fun zy : ℝ × ℝ => scalarCenteredLogCoshItoError zy.1 t zy.2) := by
  exact (continuous_scalarLogCoshItoError_uncurry t).measurable.sub
    ((measurable_scalarLogCoshBias t).comp measurable_fst)

theorem integrable_scalarCenteredLogCoshItoError (z : ℝ) (t : ℝ≥0) :
    Integrable (scalarCenteredLogCoshItoError z t) (scalarTransitionKernel t z) :=
  (integrable_scalarLogCoshItoError z t).sub (integrable_const _)

theorem integral_scalarCenteredLogCoshItoError_eq_zero (z : ℝ) (t : ℝ≥0) :
    (∫ y, scalarCenteredLogCoshItoError z t y ∂scalarTransitionKernel t z) = 0 := by
  change (∫ y, (scalarLogCoshItoError z t y - scalarLogCoshBias t z)
    ∂scalarTransitionKernel t z) = 0
  rw [integral_sub (integrable_scalarLogCoshItoError z t) (integrable_const _)]
  simp [scalarLogCoshBias]

theorem integrable_scalarCenteredLogCoshItoError_sq (z : ℝ) (t : ℝ≥0) :
    Integrable (fun y => scalarCenteredLogCoshItoError z t y ^ 2) (scalarTransitionKernel t z) := by
  have hh : (fun y => scalarCenteredLogCoshItoError z t y ^ 2) =
      fun y => scalarLogCoshItoError z t y ^ 2 -
        (2 * scalarLogCoshBias t z) * scalarLogCoshItoError z t y + scalarLogCoshBias t z ^ 2 := by
    funext y
    dsimp [scalarCenteredLogCoshItoError]
    ring
  rw [hh]
  exact ((integrable_scalarLogCoshItoError_sq z t).sub
    ((integrable_scalarLogCoshItoError z t).const_mul _)).add (integrable_const _)

theorem integral_scalarCenteredLogCoshItoError_sq_le (z : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∫ y, scalarCenteredLogCoshItoError z t y ^ 2 ∂scalarTransitionKernel t z) ≤ 6 * (t : ℝ) ^ 2 := by
  have hh : (fun y => scalarCenteredLogCoshItoError z t y ^ 2) =
      fun y => scalarLogCoshItoError z t y ^ 2 -
        (2 * scalarLogCoshBias t z) * scalarLogCoshItoError z t y + scalarLogCoshBias t z ^ 2 := by
    funext y
    dsimp [scalarCenteredLogCoshItoError]
    ring
  have hiSub : Integrable (fun y => scalarLogCoshItoError z t y ^ 2 -
      (2 * scalarLogCoshBias t z) * scalarLogCoshItoError z t y) (scalarTransitionKernel t z) := by
    have hi := (integrable_scalarLogCoshItoError_sq z t).sub
      ((integrable_scalarLogCoshItoError z t).const_mul (2 * scalarLogCoshBias t z))
    have hfun : ((fun y => scalarLogCoshItoError z t y ^ 2) -
        fun y => (2 * scalarLogCoshBias t z) * scalarLogCoshItoError z t y) =
        (fun y => scalarLogCoshItoError z t y ^ 2 -
          (2 * scalarLogCoshBias t z) * scalarLogCoshItoError z t y) := by
      funext y
      rfl
    rw [hfun] at hi
    exact hi
  rw [hh, integral_add hiSub (integrable_const _),
    integral_sub (integrable_scalarLogCoshItoError_sq z t)
      ((integrable_scalarLogCoshItoError z t).const_mul _), integral_const_mul]
  simp only [scalarLogCoshBias, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  nlinarith [integral_scalarLogCoshItoError_sq_le z t ht,
    sq_nonneg (∫ y, scalarLogCoshItoError z t y ∂scalarTransitionKernel t z)]

end SKConstants
#print axioms SKConstants.scalarLogCosh_taylor_two_abs_le
#print axioms SKConstants.integral_scalarLogCoshItoError_abs_le
#print axioms SKConstants.integral_scalarCenteredLogCoshItoError_sq_le
