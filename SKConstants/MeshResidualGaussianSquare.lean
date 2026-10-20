module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import SKConstants.ConcentrationMGF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKConstants

theorem integral_gaussian_square (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero] using h

theorem integral_centered_gaussian_square (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 - (v : ℝ) ∂gaussianReal 0 v) = 0 := by
  have hi : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  rw [integral_sub hi (integrable_const _), integral_gaussian_square]
  simp

theorem gaussian_square_exp_density (v : ℝ≥0) (θ x : ℝ) :
    gaussianPDFReal 0 v x * Real.exp (θ * (x ^ 2 - (v : ℝ))) =
      (Real.exp (-θ * (v : ℝ)) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        Real.exp (-((2 * (v : ℝ))⁻¹ - θ) * x ^ 2) := by
  unfold gaussianPDFReal
  simp only [sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  have he : -x ^ 2 / (2 * (v : ℝ)) + θ * (x ^ 2 - (v : ℝ)) =
      -θ * (v : ℝ) + -((2 * (v : ℝ))⁻¹ - θ) * x ^ 2 := by
    simp only [div_eq_mul_inv]
    ring
  rw [he, Real.exp_add]
  ring

theorem integrable_exp_centered_gaussian_square (v : ℝ≥0) (hv : v ≠ 0)
    (θ : ℝ) (hθ : θ < (2 * (v : ℝ))⁻¹) :
    Integrable (fun x : ℝ ↦ Real.exp (θ * (x ^ 2 - (v : ℝ)))) (gaussianReal 0 v) := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
    (ae_of_all _ (fun _ ↦ gaussianPDF_lt_top))).mpr
  simp only [toReal_gaussianPDF, smul_eq_mul]
  have he : (fun x : ℝ ↦ gaussianPDFReal 0 v x * Real.exp (θ * (x ^ 2 - (v : ℝ)))) =
      (fun x ↦ (Real.exp (-θ * (v : ℝ)) * (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        Real.exp (-((2 * (v : ℝ))⁻¹ - θ) * x ^ 2)) :=
    funext (gaussian_square_exp_density v θ)
  rw [he]
  exact (integrable_exp_neg_mul_sq (sub_pos.mpr hθ)).const_mul _

theorem mgf_centered_gaussian_square (v : ℝ≥0) (hv : v ≠ 0)
    (θ : ℝ) (hθ : θ < (2 * (v : ℝ))⁻¹) :
    mgf (fun x : ℝ ↦ x ^ 2 - (v : ℝ)) (gaussianReal 0 v) θ =
      Real.exp (-θ * (v : ℝ)) * (Real.sqrt (1 - 2 * (v : ℝ) * θ))⁻¹ := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast (show 0 < v from pos_iff_ne_zero.mpr hv)
  have hb : 0 < (2 * (v : ℝ))⁻¹ - θ := sub_pos.mpr hθ
  have hd : 0 < 1 - 2 * (v : ℝ) * θ := by
    have h := (lt_div_iff₀ (show 0 < 2 * (v : ℝ) by positivity)).mp
      (show θ < 1 / (2 * (v : ℝ)) by simpa only [one_div] using hθ)
    nlinarith
  have hratio :
      (Real.pi / ((2 * (v : ℝ))⁻¹ - θ)) / (2 * Real.pi * (v : ℝ)) =
        (1 - 2 * (v : ℝ) * θ)⁻¹ := by
    field_simp
  have hnorm : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
      Real.sqrt (Real.pi / ((2 * (v : ℝ))⁻¹ - θ)) =
        (Real.sqrt (1 - 2 * (v : ℝ) * θ))⁻¹ := by
    rw [mul_comm, ← div_eq_mul_inv, ← Real.sqrt_div' _ (by positivity), hratio,
      Real.sqrt_inv]
  rw [mgf, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  simp_rw [gaussian_square_exp_density]
  rw [integral_const_mul, integral_gaussian]
  rw [mul_assoc, hnorm]

theorem neg_log_square_bound (s : ℝ) (hs : |s| ≤ 1 / 4) :
    -s - Real.log (1 - 2 * s) / 2 ≤ 4 * s ^ 2 := by
  have hs' := abs_le.mp hs
  have hd : 0 < 1 - 2 * s := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have hr : (1 - 2 * s)⁻¹ - 1 - 2 * s = 4 * s ^ 2 / (1 - 2 * s) := by
    field_simp
    ring
  have hq : 4 * s ^ 2 / (1 - 2 * s) ≤ 8 * s ^ 2 := by
    rw [div_le_iff₀ hd]
    nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) (show 0 ≤ 1 / 4 - s by linarith)]
  rw [← hr] at hq
  linarith

theorem centered_gaussian_square_local_mgf (v : ℝ≥0) (hv : v ≠ 0) :
    Concentration.LocalQuadraticMGF (fun x : ℝ ↦ x ^ 2 - (v : ℝ))
      (gaussianReal 0 v) (4 * (v : ℝ) ^ 2) (1 / (4 * (v : ℝ))) := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast (show 0 < v from pos_iff_ne_zero.mpr hv)
  have hsmall : ∀ θ : ℝ, |θ| ≤ 1 / (4 * (v : ℝ)) →
      |θ * (v : ℝ)| ≤ 1 / 4 := by
    intro θ hθ
    rw [abs_mul, abs_of_pos hvR]
    rw [le_div_iff₀ (show 0 < 4 * (v : ℝ) by positivity)] at hθ
    nlinarith
  have hdomain : ∀ θ : ℝ, |θ| ≤ 1 / (4 * (v : ℝ)) →
      θ < (2 * (v : ℝ))⁻¹ := by
    intro θ hθ
    have h := (abs_le.mp (hsmall θ hθ)).2
    rw [← one_div, lt_div_iff₀ (show 0 < 2 * (v : ℝ) by positivity)]
    nlinarith
  constructor
  · intro θ hθ
    exact integrable_exp_centered_gaussian_square v hv θ (hdomain θ hθ)
  · intro θ hθ
    rw [mgf_centered_gaussian_square v hv θ (hdomain θ hθ)]
    have hd : 0 < 1 - 2 * (θ * (v : ℝ)) := by
      have h := (abs_le.mp (hsmall θ hθ)).2
      linarith
    have he : Real.exp (-θ * (v : ℝ)) * (Real.sqrt (1 - 2 * (v : ℝ) * θ))⁻¹ =
        Real.exp (-θ * (v : ℝ) - Real.log (1 - 2 * (θ * (v : ℝ))) / 2) := by
      have hroot : 0 < Real.sqrt (1 - 2 * (θ * (v : ℝ))) := Real.sqrt_pos.mpr hd
      rw [show 1 - 2 * (v : ℝ) * θ = 1 - 2 * (θ * (v : ℝ)) by ring]
      rw [Real.exp_sub, ← Real.log_sqrt hd.le, Real.exp_log hroot]
      simp only [div_eq_mul_inv]
    rw [he]
    apply Real.exp_le_exp.mpr
    have h := neg_log_square_bound (θ * (v : ℝ)) (hsmall θ hθ)
    convert h using 1 <;> ring

end SKConstants
