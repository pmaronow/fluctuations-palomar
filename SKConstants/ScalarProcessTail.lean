module

public import SKConstants.ScalarProcessKernel
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SKConstants

noncomputable def scalarDefect (y : ℝ) : ℝ := 1 - (Real.tanh y) ^ 2

noncomputable def scalarP (z : ℝ) (t : ℝ≥0) : ℝ :=
  ∫ y, scalarDefect y ∂scalarKernelLaw z t

noncomputable def scalarR (z : ℝ) (t : ℝ≥0) : ℝ :=
  ∫ y, (scalarDefect y) ^ 2 ∂scalarKernelLaw z t

theorem scalarDefect_eq_inv_cosh_sq (y : ℝ) :
    scalarDefect y = 1 / (Real.cosh y) ^ 2 := by
  unfold scalarDefect
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq y]

theorem scalarDefect_pos (y : ℝ) : 0 < scalarDefect y := by
  unfold scalarDefect
  exact sub_pos.mpr (Real.tanh_sq_lt_one y)

theorem scalarDefect_le_one (y : ℝ) : scalarDefect y ≤ 1 := by
  unfold scalarDefect
  exact sub_le_self _ (sq_nonneg _)

theorem measurable_scalarDefect : Measurable scalarDefect := by
  have he : scalarDefect = fun y ↦ 1 / (Real.cosh y) ^ 2 :=
    funext scalarDefect_eq_inv_cosh_sq
  rw [he]
  exact measurable_const.div (Real.continuous_cosh.measurable.pow_const 2)

theorem scalarKernel_mul_defect (z y : ℝ) (t : ℝ≥0) :
    scalarKernel z t y * scalarDefect y =
      (Real.exp (-(t : ℝ) / 2) / Real.cosh z) *
        (gaussianPDFReal z t y / Real.cosh y) := by
  rw [scalarDefect_eq_inv_cosh_sq]
  unfold scalarKernel
  norm_num only [Nat.cast_ofNat]
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  field_simp

theorem scalarKernel_mul_defect_sq (z y : ℝ) (t : ℝ≥0) :
    scalarKernel z t y * (scalarDefect y) ^ 2 =
      (Real.exp (-(t : ℝ) / 2) / Real.cosh z) *
        (gaussianPDFReal z t y / (Real.cosh y) ^ 3) := by
  rw [scalarDefect_eq_inv_cosh_sq]
  unfold scalarKernel
  norm_num only [Nat.cast_ofNat]
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  field_simp

theorem scalarP_eq_gaussian_integral (z : ℝ) (t : ℝ≥0) :
    scalarP z t = (Real.exp (-(t : ℝ) / 2) / Real.cosh z) *
      ∫ y, gaussianPDFReal z t y / Real.cosh y := by
  rw [scalarP, integral_scalarKernelLaw]
  simp_rw [scalarKernel_mul_defect]
  rw [integral_const_mul]

theorem scalarR_eq_gaussian_integral (z : ℝ) (t : ℝ≥0) :
    scalarR z t = (Real.exp (-(t : ℝ) / 2) / Real.cosh z) *
      ∫ y, gaussianPDFReal z t y / (Real.cosh y) ^ 3 := by
  rw [scalarR, integral_scalarKernelLaw]
  simp_rw [scalarKernel_mul_defect_sq]
  rw [integral_const_mul]

theorem measurable_scalarP (t : ℝ≥0) : Measurable (fun z ↦ scalarP z t) := by
  have hm : Measurable (fun zy : ℝ × ℝ ↦ scalarKernel zy.1 t zy.2 * scalarDefect zy.2) := by
    exact (measurable_uncurry_scalarKernel t).mul (measurable_scalarDefect.comp measurable_snd)
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  have he : (fun z ↦ scalarP z t) =
      (fun z ↦ ∫ y, scalarKernel z t y * scalarDefect y) := by
    funext z
    exact integral_scalarKernelLaw z t scalarDefect
  rw [he]
  exact h.measurable

theorem measurable_scalarR (t : ℝ≥0) : Measurable (fun z ↦ scalarR z t) := by
  have hm : Measurable (fun zy : ℝ × ℝ ↦ scalarKernel zy.1 t zy.2 * (scalarDefect zy.2) ^ 2) := by
    exact (measurable_uncurry_scalarKernel t).mul
      ((measurable_scalarDefect.comp measurable_snd).pow_const 2)
  have h := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  have he : (fun z ↦ scalarR z t) =
      (fun z ↦ ∫ y, scalarKernel z t y * (scalarDefect y) ^ 2) := by
    funext z
    exact integral_scalarKernelLaw z t (fun y ↦ (scalarDefect y) ^ 2)
  rw [he]
  exact h.measurable

theorem scalarP_nonneg (z : ℝ) (t : ℝ≥0) : 0 ≤ scalarP z t :=
  integral_nonneg (fun y ↦ (scalarDefect_pos y).le)

theorem scalarR_nonneg (z : ℝ) (t : ℝ≥0) : 0 ≤ scalarR z t :=
  integral_nonneg (fun y ↦ sq_nonneg (scalarDefect y))

theorem scalarP_le_one (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) : scalarP z t ≤ 1 := by
  have := scalarKernelLaw_isProbabilityMeasure z t ht
  have hm : AEStronglyMeasurable scalarDefect (scalarKernelLaw z t) := by
    exact measurable_scalarDefect.aestronglyMeasurable
  have hi : Integrable scalarDefect (scalarKernelLaw z t) :=
    (integrable_const (1 : ℝ)).mono' hm (ae_of_all _ (fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (scalarDefect_pos y)]
      exact scalarDefect_le_one y))
  have h := integral_mono hi (integrable_const (1 : ℝ)) scalarDefect_le_one
  simpa [scalarP] using h

theorem scalarR_le_one (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) : scalarR z t ≤ 1 := by
  have := scalarKernelLaw_isProbabilityMeasure z t ht
  have hm : AEStronglyMeasurable (fun y ↦ (scalarDefect y) ^ 2) (scalarKernelLaw z t) := by
    exact (measurable_scalarDefect.pow_const 2).aestronglyMeasurable
  have hb : ∀ y, (scalarDefect y) ^ 2 ≤ (1 : ℝ) := by
    intro y
    nlinarith [scalarDefect_pos y, scalarDefect_le_one y]
  have hi : Integrable (fun y ↦ (scalarDefect y) ^ 2) (scalarKernelLaw z t) :=
    (integrable_const (1 : ℝ)).mono' hm (ae_of_all _ (fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb y))
  have h := integral_mono hi (integrable_const (1 : ℝ)) hb
  simpa [scalarR] using h

theorem integrable_exp_neg_abs : Integrable (fun y : ℝ ↦ Real.exp (-|y|)) := by
  have hp : IntegrableOn (fun y : ℝ ↦ Real.exp (-|y|)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).congr_fun
      (fun y hy ↦ by rw [abs_of_pos hy]) measurableSet_Ioi
  have hn : IntegrableOn (fun y : ℝ ↦ Real.exp (-|y|)) (Iic 0) :=
    (integrableOn_exp_Iic 0).congr_fun
      (fun y hy ↦ by rw [abs_of_nonpos hy, neg_neg]) measurableSet_Iic
  have h := hn.union hp
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

theorem integral_exp_neg_abs : (∫ y : ℝ, Real.exp (-|y|)) = 2 := by
  rw [integral_comp_abs (f := fun y : ℝ ↦ Real.exp (-y)), integral_exp_neg_Ioi_zero]
  norm_num

theorem inv_cosh_le_exp_neg_abs (y : ℝ) :
    1 / Real.cosh y ≤ 2 * Real.exp (-|y|) := by
  have hp : 0 < Real.exp |y| := Real.exp_pos _
  have hn : 0 < Real.exp (-|y|) := Real.exp_pos _
  have hc : 0 < Real.cosh y := Real.cosh_pos _
  have he : Real.exp |y| * Real.exp (-|y|) = 1 := by
    rw [← Real.exp_add]; simp
  rw [div_le_iff₀ hc]
  rw [← Real.cosh_abs y, Real.cosh_eq]
  nlinarith

theorem integrable_inv_cosh : Integrable (fun y : ℝ ↦ 1 / Real.cosh y) := by
  refine (integrable_exp_neg_abs.const_mul 2).mono'
    (measurable_const.div Real.continuous_cosh.measurable).aestronglyMeasurable ?_
  exact ae_of_all _ (fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_cosh_le_exp_neg_abs y)

theorem integral_inv_cosh_le_four : (∫ y : ℝ, 1 / Real.cosh y) ≤ 4 := by
  calc
    _ ≤ ∫ y : ℝ, 2 * Real.exp (-|y|) :=
      integral_mono integrable_inv_cosh (integrable_exp_neg_abs.const_mul 2)
        inv_cosh_le_exp_neg_abs
    _ = 4 := by rw [integral_const_mul, integral_exp_neg_abs]; norm_num

theorem gaussianPDFReal_le_prefactor (z y : ℝ) (t : ℝ≥0) :
    gaussianPDFReal z t y ≤ (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ := by
  unfold gaussianPDFReal
  have hexp : Real.exp (-(y - z) ^ 2 / (2 * (t : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem integrable_gaussian_div_cosh (z : ℝ) (t : ℝ≥0) :
    Integrable (fun y ↦ gaussianPDFReal z t y / Real.cosh y) := by
  refine (integrable_gaussianPDFReal z t).mono'
    ((measurable_gaussianPDFReal z t).div Real.continuous_cosh.measurable).aestronglyMeasurable ?_
  exact ae_of_all _ (fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (gaussianPDFReal_nonneg z t y) (Real.cosh_pos y).le)]
    exact div_le_self (gaussianPDFReal_nonneg z t y) (Real.one_le_cosh y))

theorem scalarP_le_sharp_tail (z : ℝ) (t : ℝ≥0) :
    scalarP z t ≤ 4 * (Real.exp (-(t : ℝ) / 2) / Real.cosh z) *
      (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ := by
  rw [scalarP_eq_gaussian_integral]
  have hg : (∫ y, gaussianPDFReal z t y / Real.cosh y) ≤
      (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ * 4 := by
    calc
      _ ≤ ∫ y, (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ * (1 / Real.cosh y) := by
        apply integral_mono (integrable_gaussian_div_cosh z t)
          (integrable_inv_cosh.const_mul _)
        intro y
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_right (gaussianPDFReal_le_prefactor z y t)
            (inv_nonneg.mpr (Real.cosh_pos y).le)
      _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left integral_inv_cosh_le_four (by positivity)
  have hh := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ Real.exp (-(t : ℝ) / 2) / Real.cosh z by positivity)
  convert hh using 1
  ring

theorem integrable_gaussian_div_cosh_cube (z : ℝ) (t : ℝ≥0) :
    Integrable (fun y ↦ gaussianPDFReal z t y / (Real.cosh y) ^ 3) := by
  have hm : Measurable (fun y ↦ gaussianPDFReal z t y / (Real.cosh y) ^ 3) :=
    (measurable_gaussianPDFReal z t).div (Real.continuous_cosh.measurable.pow_const 3)
  refine (integrable_gaussianPDFReal z t).mono' hm.aestronglyMeasurable ?_
  exact ae_of_all _ (fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
      (gaussianPDFReal_nonneg z t y) (pow_nonneg (Real.cosh_pos y).le _))]
    apply div_le_self (gaussianPDFReal_nonneg z t y)
    exact one_le_pow₀ (Real.one_le_cosh y))

theorem gaussianPDFReal_lower_on_unit (z y : ℝ) (t : ℝ≥0)
    (ht : 1 ≤ (t : ℝ)) (hy : |y| ≤ 1) :
    (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ *
      Real.exp (-((1 + |z|) ^ 2) / 2) ≤ gaussianPDFReal z t y := by
  have htp : 0 < (t : ℝ) := lt_of_lt_of_le (by norm_num) ht
  have habs : |y - z| ≤ 1 + |z| :=
    (abs_sub y z).trans (by linarith)
  have hs : (y - z) ^ 2 ≤ (1 + |z|) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (y - z)) habs 2
    simpa only [sq_abs] using h
  have hh : (y - z) ^ 2 / (2 * (t : ℝ)) ≤ (1 + |z|) ^ 2 / 2 := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * (t : ℝ)) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg (1 + |z|))]
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hh

theorem gaussian_div_cosh_cube_lower_on_unit (z y : ℝ) (t : ℝ≥0)
    (ht : 1 ≤ (t : ℝ)) (hy : |y| ≤ 1) :
    ((Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ *
      Real.exp (-((1 + |z|) ^ 2) / 2)) / (Real.cosh 1) ^ 3 ≤
        gaussianPDFReal z t y / (Real.cosh y) ^ 3 := by
  have hc : Real.cosh y ≤ Real.cosh 1 :=
    Real.cosh_le_cosh.mpr (by simpa using hy)
  calc
    _ ≤ gaussianPDFReal z t y / (Real.cosh 1) ^ 3 :=
      div_le_div_of_nonneg_right (gaussianPDFReal_lower_on_unit z y t ht hy) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (gaussianPDFReal_nonneg z t y) (by positivity)
      (pow_le_pow_left₀ (Real.cosh_pos y).le hc 3)

theorem scalarR_ge_sharp_tail (z : ℝ) (t : ℝ≥0) (ht : 1 ≤ (t : ℝ)) :
    2 * (Real.exp (-(t : ℝ) / 2) / Real.cosh z) *
      ((Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ *
        Real.exp (-((1 + |z|) ^ 2) / 2) / (Real.cosh 1) ^ 3) ≤ scalarR z t := by
  rw [scalarR_eq_gaussian_integral]
  let c := (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ *
    Real.exp (-((1 + |z|) ^ 2) / 2) / (Real.cosh 1) ^ 3
  have hi := integrable_gaussian_div_cosh_cube z t
  have hc : (∫ y in Icc (-1 : ℝ) 1, c) = 2 * c := by
    rw [setIntegral_const, measureReal_def, Real.volume_Icc]
    norm_num
  have hb : 2 * c ≤ ∫ y, gaussianPDFReal z t y / (Real.cosh y) ^ 3 := by
    calc
      _ = ∫ y in Icc (-1 : ℝ) 1, c := hc.symm
      _ ≤ ∫ y in Icc (-1 : ℝ) 1, gaussianPDFReal z t y / (Real.cosh y) ^ 3 := by
        apply setIntegral_mono_on (integrableOn_const (by
          rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hi.integrableOn
          measurableSet_Icc
        intro y hy
        exact gaussian_div_cosh_cube_lower_on_unit z y t ht (abs_le.mpr hy)
      _ ≤ _ := setIntegral_le_integral hi (ae_of_all _ (fun y ↦ by
        exact div_nonneg (gaussianPDFReal_nonneg z t y) (by positivity)))
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ Real.exp (-(t : ℝ) / 2) / Real.cosh z by positivity)
  convert hh using 1
  dsimp [c]
  ring

end SKConstants
