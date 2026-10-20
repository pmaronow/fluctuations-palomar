module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKConstants

noncomputable def scalarPlusWeight (z : ℝ) : ℝ :=
  Real.exp z / (((2 : ℕ) : ℝ) * Real.cosh z)

noncomputable def scalarMinusWeight (z : ℝ) : ℝ :=
  Real.exp (-z) / (((2 : ℕ) : ℝ) * Real.cosh z)

noncomputable def scalarKernel (z : ℝ) (t : ℝ≥0) (y : ℝ) : ℝ :=
  Real.exp (-(t : ℝ) / ((2 : ℕ) : ℝ)) * gaussianPDFReal z t y *
    Real.cosh y / Real.cosh z

theorem scalarPlusWeight_pos (z : ℝ) : 0 < scalarPlusWeight z := by
  unfold scalarPlusWeight
  exact div_pos (Real.exp_pos z) (mul_pos (by norm_num) (Real.cosh_pos z))

theorem scalarMinusWeight_pos (z : ℝ) : 0 < scalarMinusWeight z := by
  unfold scalarMinusWeight
  exact div_pos (Real.exp_pos (-z)) (mul_pos (by norm_num) (Real.cosh_pos z))

theorem scalarWeight_sum (z : ℝ) : scalarPlusWeight z + scalarMinusWeight z = 1 := by
  unfold scalarPlusWeight scalarMinusWeight
  rw [← add_div, Real.cosh_eq]
  have he : Real.exp z + Real.exp (-z) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos z) (Real.exp_pos (-z)))
  field_simp
  norm_num

theorem scalarWeight_difference (z : ℝ) :
    scalarPlusWeight z - scalarMinusWeight z = Real.tanh z := by
  unfold scalarPlusWeight scalarMinusWeight
  rw [← sub_div, Real.cosh_eq, Real.tanh_eq]
  congr 1
  norm_num
  ring

theorem gaussianPDFReal_mul_exp_pos (z y : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    gaussianPDFReal z t y * Real.exp y =
      Real.exp (z + (t : ℝ) / 2) * gaussianPDFReal (z + t) t y := by
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have he : -(y - z) ^ 2 / (2 * (t : ℝ)) + y =
      z + (t : ℝ) / 2 - (y - (z + (t : ℝ))) ^ 2 / (2 * (t : ℝ)) := by
    field_simp
    ring
  simp only [gaussianPDFReal]
  rw [mul_assoc, ← Real.exp_add, he, sub_eq_add_neg, Real.exp_add]
  rw [neg_div]
  ring

theorem gaussianPDFReal_mul_exp_neg (z y : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    gaussianPDFReal z t y * Real.exp (-y) =
      Real.exp (-z + (t : ℝ) / 2) * gaussianPDFReal (z - t) t y := by
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have he : -(y - z) ^ 2 / (2 * (t : ℝ)) - y =
      -z + (t : ℝ) / 2 - (y - (z - (t : ℝ))) ^ 2 / (2 * (t : ℝ)) := by
    field_simp
    ring
  simp only [gaussianPDFReal]
  rw [mul_assoc, ← Real.exp_add]
  rw [show -(y - z) ^ 2 / (2 * (t : ℝ)) + -y =
    -(y - z) ^ 2 / (2 * (t : ℝ)) - y by ring]
  rw [he, sub_eq_add_neg, Real.exp_add, neg_div]
  ring

theorem scalarKernel_mul_plusWeight (z y : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    scalarKernel z t y * scalarPlusWeight y =
      scalarPlusWeight z * gaussianPDFReal (z + t) t y := by
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  have hgp := gaussianPDFReal_mul_exp_pos z y t ht
  have he : Real.exp (-(t : ℝ) / 2) * Real.exp (z + (t : ℝ) / 2) =
      Real.exp z := by rw [← Real.exp_add]; congr 1; ring
  unfold scalarKernel scalarPlusWeight
  norm_num only [Nat.cast_ofNat]
  calc
    _ = Real.exp (-(t : ℝ) / 2) *
      (gaussianPDFReal z t y * Real.exp y) / (2 * Real.cosh z) := by
        field_simp
    _ = _ := by rw [hgp]; simp only [← mul_assoc, he]; ring

theorem scalarKernel_mul_minusWeight (z y : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    scalarKernel z t y * scalarMinusWeight y =
      scalarMinusWeight z * gaussianPDFReal (z - t) t y := by
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  have hgm := gaussianPDFReal_mul_exp_neg z y t ht
  have he : Real.exp (-(t : ℝ) / 2) * Real.exp (-z + (t : ℝ) / 2) =
      Real.exp (-z) := by rw [← Real.exp_add]; congr 1; ring
  unfold scalarKernel scalarMinusWeight
  norm_num only [Nat.cast_ofNat]
  calc
    _ = Real.exp (-(t : ℝ) / 2) *
      (gaussianPDFReal z t y * Real.exp (-y)) / (2 * Real.cosh z) := by
        field_simp
    _ = _ := by rw [hgm]; simp only [← mul_assoc, he]; ring

theorem scalarKernel_eq_mixture (z y : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    scalarKernel z t y =
      scalarPlusWeight z * gaussianPDFReal (z + t) t y +
        scalarMinusWeight z * gaussianPDFReal (z - t) t y := by
  unfold scalarKernel scalarPlusWeight scalarMinusWeight
  norm_num only [Nat.cast_ofNat]
  rw [Real.cosh_eq]
  have hgp := gaussianPDFReal_mul_exp_pos z y t ht
  have hgm := gaussianPDFReal_mul_exp_neg z y t ht
  have heP : Real.exp (-(t : ℝ) / 2) * Real.exp (z + (t : ℝ) / 2) =
      Real.exp z := by rw [← Real.exp_add]; congr 1; ring
  have heM : Real.exp (-(t : ℝ) / 2) * Real.exp (-z + (t : ℝ) / 2) =
      Real.exp (-z) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (Real.exp (-(t : ℝ) / 2) *
        (gaussianPDFReal z t y * Real.exp y) +
          Real.exp (-(t : ℝ) / 2) *
            (gaussianPDFReal z t y * Real.exp (-y))) / (2 * Real.cosh z) := by ring
    _ = _ := by rw [hgp, hgm]; simp only [← mul_assoc, heP, heM]; ring

theorem scalarKernel_nonneg (z y : ℝ) (t : ℝ≥0) : 0 ≤ scalarKernel z t y := by
  unfold scalarKernel
  exact div_nonneg
    (mul_nonneg (mul_nonneg (Real.exp_pos _).le (gaussianPDFReal_nonneg _ _ _))
      (Real.cosh_pos _).le) (Real.cosh_pos _).le

theorem scalarKernel_pos (z y : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    0 < scalarKernel z t y := by
  unfold scalarKernel
  exact div_pos
    (mul_pos (mul_pos (Real.exp_pos _) (gaussianPDFReal_pos _ _ _ ht))
      (Real.cosh_pos _)) (Real.cosh_pos _)

theorem integrable_scalarKernel (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    Integrable (scalarKernel z t) := by
  have hfun : scalarKernel z t = fun y ↦
      scalarPlusWeight z * gaussianPDFReal (z + t) t y +
        scalarMinusWeight z * gaussianPDFReal (z - t) t y :=
    funext (fun y ↦ scalarKernel_eq_mixture z y t ht)
  rw [hfun]
  exact ((integrable_gaussianPDFReal _ _).const_mul _).add
    ((integrable_gaussianPDFReal _ _).const_mul _)

theorem integral_scalarKernel_eq_one (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∫ y, scalarKernel z t y = 1 := by
  simp_rw [scalarKernel_eq_mixture z _ t ht]
  rw [integral_add ((integrable_gaussianPDFReal _ _).const_mul _)
    ((integrable_gaussianPDFReal _ _).const_mul _), integral_const_mul,
    integral_const_mul, integral_gaussianPDFReal_eq_one _ ht,
    integral_gaussianPDFReal_eq_one _ ht]
  simpa using scalarWeight_sum z

noncomputable def scalarKernelLaw (z : ℝ) (t : ℝ≥0) : Measure ℝ :=
  volume.withDensity (fun y ↦ ENNReal.ofReal (scalarKernel z t y))

theorem scalarKernelLaw_isProbabilityMeasure (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    IsProbabilityMeasure (scalarKernelLaw z t) := by
  constructor
  rw [scalarKernelLaw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_scalarKernel z t ht)
    (ae_of_all _ (fun y ↦ scalarKernel_nonneg z y t)),
    integral_scalarKernel_eq_one z t ht]
  norm_num

theorem scalarKernel_mul_tanh (z y : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    scalarKernel z t y * Real.tanh y =
      scalarPlusWeight z * gaussianPDFReal (z + t) t y -
        scalarMinusWeight z * gaussianPDFReal (z - t) t y := by
  rw [← scalarWeight_difference y, mul_sub,
    scalarKernel_mul_plusWeight z y t ht, scalarKernel_mul_minusWeight z y t ht]

theorem integral_scalarKernel_tanh (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∫ y, scalarKernel z t y * Real.tanh y = Real.tanh z := by
  simp_rw [scalarKernel_mul_tanh z _ t ht]
  rw [integral_sub ((integrable_gaussianPDFReal _ _).const_mul _)
    ((integrable_gaussianPDFReal _ _).const_mul _), integral_const_mul,
    integral_const_mul, integral_gaussianPDFReal_eq_one _ ht,
    integral_gaussianPDFReal_eq_one _ ht]
  simpa using scalarWeight_difference z

theorem measurable_scalarKernel (z : ℝ) (t : ℝ≥0) :
    Measurable (scalarKernel z t) := by
  unfold scalarKernel
  fun_prop

theorem integral_scalarKernelLaw (z : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) :
    ∫ y, f y ∂scalarKernelLaw z t = ∫ y, scalarKernel z t y * f y := by
  unfold scalarKernelLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_scalarKernel z t).ennreal_ofReal
    (ae_of_all _ (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (scalarKernel_nonneg z _ t), smul_eq_mul]

theorem integral_tanh_scalarKernelLaw (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    ∫ y, Real.tanh y ∂scalarKernelLaw z t = Real.tanh z := by
  rw [integral_scalarKernelLaw, integral_scalarKernel_tanh z t ht]

theorem measurable_uncurry_scalarKernel (t : ℝ≥0) :
    Measurable (fun zy : ℝ × ℝ ↦ scalarKernel zy.1 t zy.2) := by
  unfold scalarKernel
  fun_prop

theorem measurable_scalarKernelLaw (t : ℝ≥0) :
    Measurable (fun z ↦ scalarKernelLaw z t) := by
  apply measurable_withDensity
  exact (measurable_uncurry_scalarKernel t).ennreal_ofReal

noncomputable def scalarTransitionKernel (t : ℝ≥0) : Kernel ℝ ℝ where
  toFun z := if t = 0 then Measure.dirac z else scalarKernelLaw z t
  measurable' := by
    by_cases ht : t = 0
    · simp only [ht, ↓reduceIte]
      exact Measure.measurable_dirac
    · simp only [ht, ↓reduceIte]
      exact measurable_scalarKernelLaw t

instance scalarTransitionKernel_isMarkov (t : ℝ≥0) :
    IsMarkovKernel (scalarTransitionKernel t) where
  isProbabilityMeasure z := by
    change IsProbabilityMeasure (if t = 0 then Measure.dirac z else scalarKernelLaw z t)
    by_cases ht : t = 0
    · simp only [ht, ↓reduceIte]
      infer_instance
    · simp only [ht, ↓reduceIte]
      exact scalarKernelLaw_isProbabilityMeasure z t ht

theorem integral_tanh_scalarTransitionKernel (z : ℝ) (t : ℝ≥0) :
    ∫ y, Real.tanh y ∂scalarTransitionKernel t z = Real.tanh z := by
  change (∫ y, Real.tanh y ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
  by_cases ht : t = 0
  · simp only [ht, ↓reduceIte]
    exact integral_dirac _ _
  · simp only [ht, ↓reduceIte]
    exact integral_tanh_scalarKernelLaw z t ht

end SKConstants
