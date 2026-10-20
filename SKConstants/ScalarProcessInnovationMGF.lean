module

public import SKConstants.ScalarProcessInnovation
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SKConstants

@[expose] def scalarSpinLaw (z : ℝ) : Measure ℝ :=
  ENNReal.ofReal (scalarPlusWeight z) • Measure.dirac 1 +
    ENNReal.ofReal (scalarMinusWeight z) • Measure.dirac (-1)

instance scalarSpinLaw_isProbabilityMeasure (z : ℝ) : IsProbabilityMeasure (scalarSpinLaw z) where
  measure_univ := by
    simp only [scalarSpinLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (scalarPlusWeight_pos z).le (scalarMinusWeight_pos z).le,
      scalarWeight_sum]
    norm_num

lemma integrable_scalarSpinLaw (z : ℝ) (f : ℝ → ℝ) : Integrable f (scalarSpinLaw z) := by
  exact ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)

lemma integral_scalarSpinLaw (z : ℝ) (f : ℝ → ℝ) :
    (∫ a, f a ∂scalarSpinLaw z) = scalarPlusWeight z * f 1 + scalarMinusWeight z * f (-1) := by
  rw [scalarSpinLaw, integral_add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (scalarPlusWeight_pos z).le,
    ENNReal.toReal_ofReal (scalarMinusWeight_pos z).le]
  rfl

lemma integral_id_scalarSpinLaw (z : ℝ) : (∫ a : ℝ, a ∂scalarSpinLaw z) = Real.tanh z := by
  rw [integral_scalarSpinLaw]
  simpa only [mul_one, mul_neg_one, sub_eq_add_neg] using scalarWeight_difference z

lemma scalarSpinLaw_mem_Icc (z : ℝ) : ∀ᵐ a ∂scalarSpinLaw z, a ∈ Set.Icc (-1) 1 := by
  rw [scalarSpinLaw, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).mpr (by norm_num)) _
  · exact Measure.ae_smul_measure ((ae_dirac_iff measurableSet_Icc).mpr (by norm_num)) _

lemma scalarSpinLaw_centered_subgaussian (z : ℝ) :
    HasSubgaussianMGF (fun a : ℝ => a - Real.tanh z) 1 (scalarSpinLaw z) := by
  have h := hasSubgaussianMGF_of_mem_Icc (X := fun a : ℝ => a) measurable_id.aemeasurable
    (scalarSpinLaw_mem_Icc z)
  rw [integral_id_scalarSpinLaw] at h
  convert h using 1
  norm_num

lemma mgf_centered_scalarSpinLaw (z theta : ℝ) :
    mgf (fun a : ℝ => a - Real.tanh z) (scalarSpinLaw z) theta =
      scalarPlusWeight z * Real.exp (theta * (1 - Real.tanh z)) +
        scalarMinusWeight z * Real.exp (theta * (-1 - Real.tanh z)) := by
  exact integral_scalarSpinLaw z _

lemma gaussianReal_integrable_exp_shift (mu c theta : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => Real.exp (theta * (y - c))) (gaussianReal mu v) := by
  have he : (fun y : ℝ => Real.exp (theta * (y - c))) =
      fun y => Real.exp (-theta * c) * Real.exp (theta * y) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (integrable_exp_mul_gaussianReal theta).const_mul _

lemma gaussianReal_integral_exp_shift (mu c theta : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, Real.exp (theta * (y - c)) ∂gaussianReal mu v) =
      Real.exp (theta * (mu - c) + (v : ℝ) * theta ^ 2 / 2) := by
  have he : (fun y : ℝ => Real.exp (theta * (y - c))) =
      fun y => Real.exp (-theta * c) * Real.exp (theta * y) := by
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_const_mul]
  change Real.exp (-theta * c) * mgf (fun y : ℝ => y) (gaussianReal mu v) theta = _
  rw [mgf_fun_id_gaussianReal, ← Real.exp_add]
  congr 1
  ring

lemma integrable_exp_scalarInnovation (z theta : ℝ) (t : ℝ≥0) :
    Integrable (fun y => Real.exp (theta * scalarInnovation z t y)) (scalarTransitionKernel t z) := by
  have he : (fun y => Real.exp (theta * scalarInnovation z t y)) =
      fun y => Real.exp (theta * (y - (z + (t : ℝ) * Real.tanh z))) := by
    funext y
    congr 1
    unfold scalarInnovation
    ring
  rw [he]
  by_cases ht : t = 0
  · change Integrable _ (if t = 0 then Measure.dirac z else scalarKernelLaw z t)
    simp only [ht, ite_true]
    exact integrable_dirac enorm_lt_top
  · change Integrable _ (if t = 0 then Measure.dirac z else scalarKernelLaw z t)
    rw [ite_eq_right ht]
    exact integrable_scalarKernelLaw_of_gaussian z t ht _
      (gaussianReal_integrable_exp_shift _ _ _ _) (gaussianReal_integrable_exp_shift _ _ _ _)

lemma mgf_scalarInnovation_exact (z theta : ℝ) (t : ℝ≥0) :
    mgf (scalarInnovation z t) (scalarTransitionKernel t z) theta =
      Real.exp ((t : ℝ) * theta ^ 2 / 2) *
        (scalarPlusWeight z * Real.exp ((theta * t) * (1 - Real.tanh z)) +
          scalarMinusWeight z * Real.exp ((theta * t) * (-1 - Real.tanh z))) := by
  by_cases ht : t = 0
  · change (∫ y, Real.exp (theta * scalarInnovation z t y)
      ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
    simp only [ht, ite_true, integral_dirac, scalarInnovation, NNReal.coe_zero, zero_mul,
      sub_self, sub_zero, mul_zero, zero_div, Real.exp_zero, mul_one, one_mul]
    exact (scalarWeight_sum z).symm
  · have he : (fun y => Real.exp (theta * scalarInnovation z t y)) =
        fun y => Real.exp (theta * (y - (z + (t : ℝ) * Real.tanh z))) := by
      funext y
      congr 1
      unfold scalarInnovation
      ring
    unfold mgf
    rw [he]
    change (∫ y, Real.exp (theta * (y - (z + (t : ℝ) * Real.tanh z)))
      ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
    rw [ite_eq_right ht, integral_scalarKernelLaw_mixture z t ht _
      (gaussianReal_integrable_exp_shift _ _ _ _) (gaussianReal_integrable_exp_shift _ _ _ _),
      gaussianReal_integral_exp_shift, gaussianReal_integral_exp_shift]
    have hp : theta * (z + (t : ℝ) - (z + (t : ℝ) * Real.tanh z)) + (t : ℝ) * theta ^ 2 / 2 =
        (t : ℝ) * theta ^ 2 / 2 + (theta * t) * (1 - Real.tanh z) := by ring
    have hm : theta * (z - (t : ℝ) - (z + (t : ℝ) * Real.tanh z)) + (t : ℝ) * theta ^ 2 / 2 =
        (t : ℝ) * theta ^ 2 / 2 + (theta * t) * (-1 - Real.tanh z) := by ring
    rw [hp, hm, Real.exp_add, Real.exp_add]
    ring

lemma mgf_scalarInnovation_le (z theta : ℝ) (t : ℝ≥0) :
    mgf (scalarInnovation z t) (scalarTransitionKernel t z) theta ≤
      Real.exp (theta ^ 2 * ((t : ℝ) + (t : ℝ) ^ 2) / 2) := by
  rw [mgf_scalarInnovation_exact, ← mgf_centered_scalarSpinLaw]
  have h := (scalarSpinLaw_centered_subgaussian z).mgf_le (theta * t)
  have hp := mul_le_mul_of_nonneg_left h (Real.exp_pos ((t : ℝ) * theta ^ 2 / 2)).le
  simp only [NNReal.coe_one, one_mul] at hp
  rw [← Real.exp_add] at hp
  convert hp using 1
  congr 1
  ring

lemma scalarInnovation_subgaussian (z : ℝ) (t : ℝ≥0) :
    HasSubgaussianMGF (scalarInnovation z t) (t + t ^ 2) (scalarTransitionKernel t z) where
  integrable_exp_mul theta := integrable_exp_scalarInnovation z theta t
  mgf_le theta := by
    simpa only [NNReal.coe_add, NNReal.coe_pow, mul_comm] using mgf_scalarInnovation_le z theta t

lemma scalarInnovation_scaled_subgaussian (z a : ℝ) (t : ℝ≥0) :
    HasSubgaussianMGF (fun y => a * scalarInnovation z t y)
      (⟨a ^ 2, sq_nonneg a⟩ * (t + t ^ 2)) (scalarTransitionKernel t z) :=
  (scalarInnovation_subgaussian z t).const_mul a

end SKConstants
