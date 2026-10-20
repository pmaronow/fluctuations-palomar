module

public import SKConstants.ScalarProcessSemigroup
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SKConstants

lemma hasDerivAt_scalar_tanh (x : ℝ) : HasDerivAt Real.tanh (scalarDefect x) x := by
  have hd := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have he : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
      (Real.cosh x) ^ 2 = scalarDefect x := by
    rw [scalarDefect_eq_inv_cosh_sq]
    congr 1
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  convert hd using 1
  · exact funext Real.tanh_eq_sinh_div_cosh
  · exact he.symm

lemma scalar_tanh_lipschitz : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_scalar_tanh x).differentiableAt)
  intro x
  rw [(hasDerivAt_scalar_tanh x).deriv]
  change |scalarDefect x| ≤ 1
  rw [abs_of_pos (scalarDefect_pos x)]
  exact scalarDefect_le_one x

lemma scalar_tanh_abs_sub_le (y z : ℝ) : |Real.tanh y - Real.tanh z| ≤ |y - z| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using scalar_tanh_lipschitz.dist_le_mul y z

lemma gaussianReal_integrable_pow (mu : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n) (gaussianReal mu v) := by
  exact integrable_pow_of_mem_interior_integrableExpSet (X := fun y : ℝ => y) (by simp) n

lemma gaussianReal_integral_fourth (mu : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, y ^ 4 ∂gaussianReal mu v) = mu ^ 4 + 6 * (v : ℝ) * mu ^ 2 + 3 * (v : ℝ) ^ 2 := by
  let P : ℝ → ℝ := fun t => mu + (v : ℝ) * t
  let F : ℝ → ℝ := fun t => Real.exp (mu * t + (v : ℝ) * t ^ 2 / 2)
  have hP : ∀ t, HasDerivAt P (v : ℝ) t := by
    intro t
    convert (hasDerivAt_const t mu).add
      ((hasDerivAt_const t (v : ℝ)).mul (hasDerivAt_id t)) using 1
    · rfl
    · simp
  have hF : ∀ t, HasDerivAt F (P t * F t) t := by
    intro t
    convert (((hasDerivAt_const t mu).mul (hasDerivAt_id t)).add
      (((hasDerivAt_const t (v : ℝ)).mul ((hasDerivAt_id t).pow 2)).div_const 2)).exp
      using 1
    all_goals dsimp [P, F]
    all_goals ring
  have d1 : deriv F = fun t => P t * F t := funext fun t => (hF t).deriv
  have d2 : deriv (fun t => P t * F t) = fun t => (P t ^ 2 + (v : ℝ)) * F t := by
    funext t
    convert ((hP t).mul (hF t)).deriv using 1
    ring
  have d3 : deriv (fun t => (P t ^ 2 + (v : ℝ)) * F t) =
      fun t => (P t ^ 3 + 3 * (v : ℝ) * P t) * F t := by
    funext t
    convert (((hP t).pow 2).add_const (v : ℝ) |>.mul (hF t)).deriv using 1
    simp only [Pi.pow_apply]
    ring
  have d4 : deriv (fun t => (P t ^ 3 + 3 * (v : ℝ) * P t) * F t) =
      fun t => (P t ^ 4 + 6 * (v : ℝ) * P t ^ 2 + 3 * (v : ℝ) ^ 2) * F t := by
    funext t
    convert (((hP t).pow 3).add ((hP t).const_mul (3 * (v : ℝ))) |>.mul (hF t)).deriv
      using 1
    simp only [Pi.pow_apply, Pi.add_apply]
    ring
  have hmoment := iteratedDeriv_mgf_zero (X := fun y : ℝ => y)
    (μ := gaussianReal mu v) (by simp) 4
  simp only [Pi.pow_apply] at hmoment
  rw [← hmoment, mgf_fun_id_gaussianReal]
  change iteratedDeriv 4 F 0 = _
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (deriv (deriv F))) 0 = _
  rw [d1, d2, d3, d4]
  simp [P, F]

lemma gaussianReal_integrable_shift_pow (mu c : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun y : ℝ => (y - c) ^ n) (gaussianReal mu v) := by
  have h := gaussianReal_integrable_pow (mu - c) v n
  rw [← gaussianReal_map_sub_const (μ := mu) (v := v) c] at h
  exact h.comp_measurable (by fun_prop)

lemma gaussianReal_integral_shift_fourth (mu c : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - c) ^ 4 ∂gaussianReal mu v) =
      (mu - c) ^ 4 + 6 * (v : ℝ) * (mu - c) ^ 2 + 3 * (v : ℝ) ^ 2 := by
  calc
    _ = ∫ y : ℝ, y ^ 4 ∂(gaussianReal mu v).map (fun y => y - c) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = _ := by rw [gaussianReal_map_sub_const, gaussianReal_integral_fourth]

@[expose] def scalarPosteriorIncrement (z y : ℝ) : ℝ := Real.tanh y - Real.tanh z

lemma scalar_tanh_abs_le_one (y : ℝ) : |Real.tanh y| ≤ 1 := by
  nlinarith [Real.tanh_sq_lt_one y, sq_abs (Real.tanh y), abs_nonneg (Real.tanh y)]

lemma scalarPosteriorIncrement_abs_le_two (z y : ℝ) : |scalarPosteriorIncrement z y| ≤ 2 := by
  exact (abs_sub _ _).trans (by linarith [scalar_tanh_abs_le_one y, scalar_tanh_abs_le_one z])

lemma measurable_scalarPosteriorIncrement (z : ℝ) : Measurable (scalarPosteriorIncrement z) :=
  scalar_tanh_lipschitz.continuous.measurable.sub_const _

lemma integrable_scalarPosteriorIncrement_pow (z : ℝ) (t : ℝ≥0) (n : ℕ) :
    Integrable (fun y => scalarPosteriorIncrement z y ^ n) (scalarTransitionKernel t z) := by
  apply Integrable.of_bound ((measurable_scalarPosteriorIncrement z).pow_const n).aestronglyMeasurable
    (2 ^ n)
  exact ae_of_all _ (fun y => by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (scalarPosteriorIncrement_abs_le_two z y) n)

lemma integral_scalarPosteriorIncrement_eq_zero (z : ℝ) (t : ℝ≥0) :
    (∫ y, scalarPosteriorIncrement z y ∂scalarTransitionKernel t z) = 0 := by
  have hi : Integrable Real.tanh (scalarTransitionKernel t z) :=
    Integrable.of_bound scalar_tanh_lipschitz.continuous.measurable.aestronglyMeasurable 1
      (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using scalar_tanh_abs_le_one y))
  unfold scalarPosteriorIncrement
  rw [integral_sub hi (integrable_const _), integral_tanh_scalarTransitionKernel]
  simp

lemma integrable_scalarField_displacement_pow (z : ℝ) (t : ℝ≥0) (n : ℕ) :
    Integrable (fun y : ℝ => (y - z) ^ n) (scalarTransitionKernel t z) := by
  by_cases ht : t = 0
  · subst t
    rw [scalarTransitionKernel_zero]
    exact integrable_dirac enorm_lt_top
  · change Integrable _ (if t = 0 then Measure.dirac z else scalarKernelLaw z t)
    rw [ite_eq_right ht]
    exact integrable_scalarKernelLaw_of_gaussian z t ht _
      (gaussianReal_integrable_shift_pow _ _ _ n) (gaussianReal_integrable_shift_pow _ _ _ n)

lemma integral_scalarField_displacement_sq (z : ℝ) (t : ℝ≥0) :
    (∫ y : ℝ, (y - z) ^ 2 ∂scalarTransitionKernel t z) = (t : ℝ) + (t : ℝ) ^ 2 := by
  by_cases ht : t = 0
  · subst t
    rw [scalarTransitionKernel_zero]
    simp [Kernel.id_apply, integral_dirac]
  · change (∫ y : ℝ, (y - z) ^ 2 ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
    rw [ite_eq_right ht, integral_scalarKernelLaw_mixture z t ht _
      (gaussianReal_integrable_shift_sq _ _ _) (gaussianReal_integrable_shift_sq _ _ _),
      gaussianReal_integral_shift_sq, gaussianReal_integral_shift_sq]
    have he : z + (t : ℝ) - z = t := by ring
    have he' : z - (t : ℝ) - z = -(t : ℝ) := by ring
    rw [he, he', neg_sq, ← add_mul, scalarWeight_sum]
    ring

lemma integral_scalarField_displacement_fourth (z : ℝ) (t : ℝ≥0) :
    (∫ y : ℝ, (y - z) ^ 4 ∂scalarTransitionKernel t z) =
      3 * (t : ℝ) ^ 2 + 6 * (t : ℝ) ^ 3 + (t : ℝ) ^ 4 := by
  by_cases ht : t = 0
  · subst t
    rw [scalarTransitionKernel_zero]
    simp [Kernel.id_apply, integral_dirac]
  · change (∫ y : ℝ, (y - z) ^ 4 ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
    rw [ite_eq_right ht, integral_scalarKernelLaw_mixture z t ht _
      (gaussianReal_integrable_shift_pow _ _ _ 4) (gaussianReal_integrable_shift_pow _ _ _ 4),
      gaussianReal_integral_shift_fourth, gaussianReal_integral_shift_fourth]
    have he : z + (t : ℝ) - z = t := by ring
    have he' : z - (t : ℝ) - z = -(t : ℝ) := by ring
    rw [he, he']
    have hneg4 : (-(t : ℝ)) ^ 4 = (t : ℝ) ^ 4 := by ring
    rw [hneg4, neg_sq, ← add_mul, scalarWeight_sum]
    ring

lemma integral_scalarPosteriorIncrement_sq_le (z : ℝ) (t : ℝ≥0) :
    (∫ y, scalarPosteriorIncrement z y ^ 2 ∂scalarTransitionKernel t z) ≤
      (t : ℝ) + (t : ℝ) ^ 2 := by
  rw [← integral_scalarField_displacement_sq]
  apply integral_mono (integrable_scalarPosteriorIncrement_pow z t 2)
    (integrable_scalarField_displacement_pow z t 2)
  intro y
  exact (sq_le_sq).mpr (scalar_tanh_abs_sub_le y z)

lemma integral_scalarPosteriorIncrement_fourth_le (z : ℝ) (t : ℝ≥0) :
    (∫ y, scalarPosteriorIncrement z y ^ 4 ∂scalarTransitionKernel t z) ≤
      3 * (t : ℝ) ^ 2 + 6 * (t : ℝ) ^ 3 + (t : ℝ) ^ 4 := by
  rw [← integral_scalarField_displacement_fourth]
  apply integral_mono (integrable_scalarPosteriorIncrement_pow z t 4)
    (integrable_scalarField_displacement_pow z t 4)
  intro y
  have h := pow_le_pow_left₀ (abs_nonneg (Real.tanh y - Real.tanh z))
    (scalar_tanh_abs_sub_le y z) 4
  simpa only [scalarPosteriorIncrement, Even.pow_abs (by decide : Even 4)] using h

lemma integral_scalarPosteriorIncrement_sq_le_two_mul (z : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∫ y, scalarPosteriorIncrement z y ^ 2 ∂scalarTransitionKernel t z) ≤ 2 * (t : ℝ) := by
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have ht0 := t.coe_nonneg
  have hs := mul_le_mul_of_nonneg_left htR ht0
  exact (integral_scalarPosteriorIncrement_sq_le z t).trans (by nlinarith)

lemma integral_scalarPosteriorIncrement_fourth_le_ten_mul (z : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∫ y, scalarPosteriorIncrement z y ^ 4 ∂scalarTransitionKernel t z) ≤ 10 * (t : ℝ) ^ 2 := by
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have ht0 := t.coe_nonneg
  have h3 : (t : ℝ) ^ 3 ≤ (t : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left htR (sq_nonneg (t : ℝ))]
  have h4 : (t : ℝ) ^ 4 ≤ (t : ℝ) ^ 2 := by
    have hs : (t : ℝ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg (t : ℝ))]
  exact (integral_scalarPosteriorIncrement_fourth_le z t).trans (by nlinarith)

lemma scalarPosteriorIncrement_local_mgf (z : ℝ) (t : ℝ≥0) :
    Concentration.LocalQuadraticMGF (scalarPosteriorIncrement z) (scalarTransitionKernel t z)
      ((t : ℝ) + (t : ℝ) ^ 2) (1 / 2) := by
  exact Concentration.localQuadraticMGF_of_bounded_variance
    (measurable_scalarPosteriorIncrement z) (by norm_num : (0 : ℝ) < 2)
    (ae_of_all _ (fun y => scalarPosteriorIncrement_abs_le_two z y))
    (integral_scalarPosteriorIncrement_eq_zero z t) (integral_scalarPosteriorIncrement_sq_le z t)

lemma scalarPosteriorIncrement_bernstein (z : ℝ) (t : ℝ≥0) (ht : 0 < t)
    (eta : ℝ) (heta : 0 < eta) :
    (scalarTransitionKernel t z).real {y | eta ≤ |scalarPosteriorIncrement z y|} ≤
      2 * Real.exp (-min (eta ^ 2 / (4 * ((t : ℝ) + (t : ℝ) ^ 2))) (eta / 4)) := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have h := Concentration.localQuadraticMGF_two_sided
    (scalarPosteriorIncrement_local_mgf z t) (by positivity) (by norm_num) heta
  have he : (1 / 2 : ℝ) * eta / 2 = eta / 4 := by ring
  simpa only [he] using h

end SKConstants
