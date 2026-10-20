module
public import SKConstants.ScalarProcessHistory
public import SKConstants.ScalarProcessInnovationMGF
public import SKConstants.ScalarProcessPosteriorIncrement
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma gaussianReal_integrable_char_shift (mu c theta : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => Complex.exp (((theta * (y - c) : ℝ) : ℂ) * Complex.I))
      (gaussianReal mu v) := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun y => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl])

lemma gaussianReal_integral_char_shift (mu c theta : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, Complex.exp (((theta * (y - c) : ℝ) : ℂ) * Complex.I)
      ∂gaussianReal mu v) =
      Complex.exp (((theta * (mu - c) : ℝ) : ℂ) * Complex.I -
        (((v : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ)) := by
  have he : (fun y : ℝ => Complex.exp (((theta * (y - c) : ℝ) : ℂ) * Complex.I)) =
      fun y => Complex.exp (((-theta * c : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((theta * y : ℝ) : ℂ) * Complex.I) := by
    funext y
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_const_mul]
  simp only [Complex.ofReal_mul]
  rw [← charFun_apply_real, charFun_gaussianReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[expose] def scalarInnovationChar (z : ℝ) (t : ℝ≥0) (theta : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (((theta * scalarInnovation z t y : ℝ) : ℂ) * Complex.I)
    ∂scalarTransitionKernel t z

lemma scalarInnovationChar_exact (z theta : ℝ) (t : ℝ≥0) :
    scalarInnovationChar z t theta =
      Complex.exp (-(((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ)) *
        ((scalarPlusWeight z : ℂ) *
          Complex.exp ((((theta * t) * (1 - Real.tanh z) : ℝ) : ℂ) * Complex.I) +
        (scalarMinusWeight z : ℂ) *
          Complex.exp ((((theta * t) * (-1 - Real.tanh z) : ℝ) : ℂ) * Complex.I)) := by
  unfold scalarInnovationChar
  by_cases ht : t = 0
  · change (∫ y : ℝ, _ ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
    simp only [ht, ite_true, integral_dirac, scalarInnovation, NNReal.coe_zero, zero_mul,
      sub_self, sub_zero, mul_zero, zero_div, Complex.ofReal_zero, neg_zero,
      Complex.exp_zero, mul_one, one_mul]
    exact_mod_cast (scalarWeight_sum z).symm
  · have he : (fun y => Complex.exp (((theta * scalarInnovation z t y : ℝ) : ℂ) * Complex.I)) =
        fun y => Complex.exp (((theta * (y - (z + (t : ℝ) * Real.tanh z)) : ℝ) : ℂ) *
          Complex.I) := by
      funext y
      have hy : scalarInnovation z t y = y - (z + (t : ℝ) * Real.tanh z) := by
        unfold scalarInnovation
        ring
      rw [hy]
    rw [he]
    change (∫ y : ℝ, _ ∂if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
    rw [ite_eq_right ht, scalarKernelLaw_eq_mixture z t ht,
      integral_add_measure
        ((gaussianReal_integrable_char_shift _ _ _ _).smul_measure ENNReal.ofReal_ne_top)
        ((gaussianReal_integrable_char_shift _ _ _ _).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (scalarPlusWeight_pos z).le,
      ENNReal.toReal_ofReal (scalarMinusWeight_pos z).le]
    simp only [Complex.real_smul]
    rw [gaussianReal_integral_char_shift, gaussianReal_integral_char_shift]
    have hp : (((theta * (z + (t : ℝ) - (z + (t : ℝ) * Real.tanh z)) : ℝ) : ℂ) * Complex.I -
        (((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ)) =
        -(((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ) +
        ((((theta * t) * (1 - Real.tanh z) : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    have hm : (((theta * (z - (t : ℝ) - (z + (t : ℝ) * Real.tanh z)) : ℝ) : ℂ) * Complex.I -
        (((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ)) =
        -(((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ) +
        ((((theta * t) * (-1 - Real.tanh z) : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [hp, hm, Complex.exp_add, Complex.exp_add]
    ring

lemma complex_exp_imag_remainder_le (u : ℝ) :
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I‖ ≤
      u ^ 2 * Real.exp |u| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((u : ℂ) * Complex.I) 2
  simpa [Finset.sum_range_succ, Complex.norm_mul, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, sub_sub] using h

lemma scalarSpin_centered_first (z : ℝ) :
    scalarPlusWeight z * (1 - Real.tanh z) +
      scalarMinusWeight z * (-1 - Real.tanh z) = 0 := by
  calc
    _ = (scalarPlusWeight z - scalarMinusWeight z) -
      (scalarPlusWeight z + scalarMinusWeight z) * Real.tanh z := by ring
    _ = 0 := by rw [scalarWeight_sum, scalarWeight_difference]; ring

lemma scalarSpin_centered_second (z : ℝ) :
    scalarPlusWeight z * (1 - Real.tanh z) ^ 2 +
      scalarMinusWeight z * (-1 - Real.tanh z) ^ 2 = 1 - Real.tanh z ^ 2 := by
  calc
    _ = (scalarPlusWeight z + scalarMinusWeight z) * (1 + Real.tanh z ^ 2) -
      2 * Real.tanh z * (scalarPlusWeight z - scalarMinusWeight z) := by ring
    _ = _ := by rw [scalarWeight_sum, scalarWeight_difference]; ring

lemma scalarSpin_char_remainder (z theta : ℝ) :
    ‖(scalarPlusWeight z : ℂ) *
        Complex.exp (((theta * (1 - Real.tanh z) : ℝ) : ℂ) * Complex.I) +
      (scalarMinusWeight z : ℂ) *
        Complex.exp (((theta * (-1 - Real.tanh z) : ℝ) : ℂ) * Complex.I) - 1‖ ≤
      theta ^ 2 * Real.exp (2 * |theta|) := by
  let up : ℝ := theta * (1 - Real.tanh z)
  let um : ℝ := theta * (-1 - Real.tanh z)
  have hsum : (scalarPlusWeight z : ℂ) + (scalarMinusWeight z : ℂ) = 1 := by
    exact_mod_cast scalarWeight_sum z
  have hcenter : (scalarPlusWeight z : ℂ) * ((up : ℂ) * Complex.I) +
      (scalarMinusWeight z : ℂ) * ((um : ℂ) * Complex.I) = 0 := by
    have hreal : scalarPlusWeight z * up + scalarMinusWeight z * um = 0 := by
      dsimp [up, um]
      calc
        _ = theta * (scalarPlusWeight z * (1 - Real.tanh z) +
          scalarMinusWeight z * (-1 - Real.tanh z)) := by ring
        _ = 0 := by rw [scalarSpin_centered_first, mul_zero]
    calc
      _ = ((scalarPlusWeight z * up + scalarMinusWeight z * um : ℝ) : ℂ) *
        Complex.I := by push_cast; ring
      _ = 0 := by rw [hreal]; simp
  have hid : (scalarPlusWeight z : ℂ) * Complex.exp ((up : ℂ) * Complex.I) +
      (scalarMinusWeight z : ℂ) * Complex.exp ((um : ℂ) * Complex.I) - 1 =
      (scalarPlusWeight z : ℂ) *
        (Complex.exp ((up : ℂ) * Complex.I) - 1 - (up : ℂ) * Complex.I) +
      (scalarMinusWeight z : ℂ) *
        (Complex.exp ((um : ℂ) * Complex.I) - 1 - (um : ℂ) * Complex.I) := by
    linear_combination hsum + hcenter
  have hp : |up| ≤ 2 * |theta| := by
    dsimp [up]
    rw [abs_mul]
    have hd : |1 - Real.tanh z| ≤ 2 := (abs_sub _ _).trans (by
      simp only [abs_one]
      linarith [scalar_tanh_abs_le_one z])
    nlinarith [abs_nonneg theta]
  have hm : |um| ≤ 2 * |theta| := by
    dsimp [um]
    rw [abs_mul]
    have hd : |-1 - Real.tanh z| ≤ 2 := (abs_sub _ _).trans (by
      simp only [abs_neg, abs_one]
      linarith [scalar_tanh_abs_le_one z])
    nlinarith [abs_nonneg theta]
  have hvar : scalarPlusWeight z * up ^ 2 + scalarMinusWeight z * um ^ 2 ≤ theta ^ 2 := by
    dsimp [up, um]
    calc
      _ = theta ^ 2 * (scalarPlusWeight z * (1 - Real.tanh z) ^ 2 +
        scalarMinusWeight z * (-1 - Real.tanh z) ^ 2) := by ring
      _ = theta ^ 2 * (1 - Real.tanh z ^ 2) := by rw [scalarSpin_centered_second]
      _ ≤ theta ^ 2 := by nlinarith [sq_nonneg theta, sq_nonneg (Real.tanh z)]
  change ‖(scalarPlusWeight z : ℂ) * Complex.exp ((up : ℂ) * Complex.I) +
    (scalarMinusWeight z : ℂ) * Complex.exp ((um : ℂ) * Complex.I) - 1‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖(scalarPlusWeight z : ℂ) *
        (Complex.exp ((up : ℂ) * Complex.I) - 1 - (up : ℂ) * Complex.I)‖ +
      ‖(scalarMinusWeight z : ℂ) *
        (Complex.exp ((um : ℂ) * Complex.I) - 1 - (um : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ = scalarPlusWeight z *
        ‖Complex.exp ((up : ℂ) * Complex.I) - 1 - (up : ℂ) * Complex.I‖ +
      scalarMinusWeight z *
        ‖Complex.exp ((um : ℂ) * Complex.I) - 1 - (um : ℂ) * Complex.I‖ := by
      simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (scalarPlusWeight_pos z), abs_of_pos (scalarMinusWeight_pos z)]
    _ ≤ scalarPlusWeight z * (up ^ 2 * Real.exp (2 * |theta|)) +
      scalarMinusWeight z * (um ^ 2 * Real.exp (2 * |theta|)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (scalarPlusWeight_pos z).le
        exact (complex_exp_imag_remainder_le up).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) (sq_nonneg up))
      · apply mul_le_mul_of_nonneg_left _ (scalarMinusWeight_pos z).le
        exact (complex_exp_imag_remainder_le um).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) (sq_nonneg um))
    _ = (scalarPlusWeight z * up ^ 2 + scalarMinusWeight z * um ^ 2) *
      Real.exp (2 * |theta|) := by ring
    _ ≤ theta ^ 2 * Real.exp (2 * |theta|) := by gcongr

lemma scalarInnovationChar_eq_charFun (z theta : ℝ) (t : ℝ≥0) :
    scalarInnovationChar z t theta =
      charFun ((scalarTransitionKernel t z).map (scalarInnovation z t)) theta := by
  rw [charFun_apply_real, integral_map
    (by unfold scalarInnovation; fun_prop) (by fun_prop)]
  simp only [scalarInnovationChar, Complex.ofReal_mul]

lemma scalarInnovationChar_gaussian_error (z theta : ℝ) (t : ℝ≥0) :
    ‖scalarInnovationChar z t theta -
      Complex.exp (-(((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      theta ^ 2 * (t : ℝ) ^ 2 * Real.exp (2 * |theta| * t) := by
  rw [scalarInnovationChar_exact]
  let G : ℂ := Complex.exp (-(((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ))
  let S : ℂ := (scalarPlusWeight z : ℂ) *
      Complex.exp ((((theta * t) * (1 - Real.tanh z) : ℝ) : ℂ) * Complex.I) +
    (scalarMinusWeight z : ℂ) *
      Complex.exp ((((theta * t) * (-1 - Real.tanh z) : ℝ) : ℂ) * Complex.I)
  have hG : ‖G‖ ≤ 1 := by
    dsimp [G]
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (t : ℝ) * theta ^ 2 / 2 := by positivity
    linarith
  change ‖G * S - G‖ ≤ _
  calc
    _ = ‖G‖ * ‖S - 1‖ := by
      have he : G * S - G = G * (S - 1) := by ring
      rw [he, norm_mul]
    _ ≤ 1 * ((theta * t) ^ 2 * Real.exp (2 * |theta * t|)) :=
      mul_le_mul hG (scalarSpin_char_remainder z (theta * t)) (norm_nonneg _) zero_le_one
    _ = theta ^ 2 * (t : ℝ) ^ 2 * Real.exp (2 * |theta| * t) := by
      have ha : |(t : ℝ)| = (t : ℝ) := abs_of_nonneg t.property
      simp only [abs_mul, ha]
      ring_nf

lemma scalarInnovationChar_gaussian_error_le (z theta : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    ‖scalarInnovationChar z t theta -
      Complex.exp (-(((t : ℝ) * theta ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      (theta ^ 2 * Real.exp (2 * |theta|)) * (t : ℝ) ^ 2 := by
  apply (scalarInnovationChar_gaussian_error z theta t).trans
  have htR : (t : ℝ) ≤ 1 := ht
  calc
    _ ≤ theta ^ 2 * (t : ℝ) ^ 2 * Real.exp (2 * |theta|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg theta]
    _ = _ := by ring

lemma charFun_scalarInnovation_gaussian_error (z theta : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    ‖charFun ((scalarTransitionKernel t z).map (scalarInnovation z t)) theta -
      charFun (gaussianReal 0 t) theta‖ ≤
      (theta ^ 2 * Real.exp (2 * |theta|)) * (t : ℝ) ^ 2 := by
  rw [← scalarInnovationChar_eq_charFun, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_ofNat] using scalarInnovationChar_gaussian_error_le z theta t ht

@[expose] def scalarHistoryWeightedInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) :
    (n : ℕ) → ScalarObservationHistory n → ℝ
  | 0, _ => 0
  | n + 1, h => scalarHistoryWeightedInnovationSum z dt a n h.1 +
      a n * scalarInnovation (scalarLastField z n h.1) (dt n) h.2

@[fun_prop] lemma measurable_scalarHistoryWeightedInnovationSum
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    Measurable (scalarHistoryWeightedInnovationSum z dt a n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add
      ((measurable_scalarHistoryInnovationStep z (dt n) n).const_mul (a n))

lemma integrable_char_scalarHistoryWeightedInnovationSum
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    Integrable (fun h => Complex.exp ((scalarHistoryWeightedInnovationSum z dt a n h : ℂ) *
      Complex.I)) (scalarObservationHistoryLaw z dt n) := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun h => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl])

@[expose] def scalarHistoryWeightedInnovationChar
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) : ℂ :=
  ∫ h, Complex.exp ((scalarHistoryWeightedInnovationSum z dt a n h : ℂ) * Complex.I)
    ∂scalarObservationHistoryLaw z dt n

lemma scalarHistoryWeightedInnovationChar_succ
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    scalarHistoryWeightedInnovationChar z dt a (n + 1) =
      ∫ h, Complex.exp ((scalarHistoryWeightedInnovationSum z dt a n h : ℂ) * Complex.I) *
        scalarInnovationChar (scalarLastField z n h) (dt n) (a n)
        ∂scalarObservationHistoryLaw z dt n := by
  unfold scalarHistoryWeightedInnovationChar
  change (∫ p : ScalarObservationHistory n × ℝ,
    Complex.exp ((scalarHistoryWeightedInnovationSum z dt a (n + 1) p : ℂ) * Complex.I)
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) = _
  rw [Measure.integral_compProd
    (integrable_char_scalarHistoryWeightedInnovationSum z dt a (n + 1))]
  congr 1
  funext h
  have he : (fun y => Complex.exp
      ((scalarHistoryWeightedInnovationSum z dt a (n + 1) (h, y) : ℂ) * Complex.I)) =
      (fun y => Complex.exp ((scalarHistoryWeightedInnovationSum z dt a n h : ℂ) * Complex.I) *
        Complex.exp (((a n * scalarInnovation (scalarLastField z n h) (dt n) y : ℝ) : ℂ) *
          Complex.I)) := by
    funext y
    simp only [scalarHistoryWeightedInnovationSum, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [he, integral_const_mul]
  rfl

lemma scalarInnovationChar_norm_le_one (z theta : ℝ) (t : ℝ≥0) :
    ‖scalarInnovationChar z t theta‖ ≤ 1 := by
  apply (norm_integral_le_of_norm_le_const
    (μ := scalarTransitionKernel t z) (C := (1 : ℝ))
    (ae_of_all _ (fun y => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl]))).trans_eq
  simp

lemma norm_exp_neg_ofReal_le_one (x : ℝ) (hx : 0 ≤ x) :
    ‖Complex.exp (-(x : ℂ))‖ ≤ 1 := by
  rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)

lemma scalarHistoryWeightedInnovationChar_succ_error
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    ‖scalarHistoryWeightedInnovationChar z dt a (n + 1) -
      Complex.exp (-(((dt n : ℝ) * (a n) ^ 2 / 2 : ℝ) : ℂ)) *
        scalarHistoryWeightedInnovationChar z dt a n‖ ≤
      (a n) ^ 2 * (dt n : ℝ) ^ 2 * Real.exp (2 * |a n| * dt n) := by
  let E : ScalarObservationHistory n → ℂ := fun h =>
    Complex.exp ((scalarHistoryWeightedInnovationSum z dt a n h : ℂ) * Complex.I)
  let S : ScalarObservationHistory n → ℂ := fun h =>
    scalarInnovationChar (scalarLastField z n h) (dt n) (a n)
  let G : ℂ := Complex.exp (-(((dt n : ℝ) * (a n) ^ 2 / 2 : ℝ) : ℂ))
  have hS : StronglyMeasurable S := by
    have hm : StronglyMeasurable (fun p : ScalarObservationHistory n × ℝ =>
        Complex.exp (((a n * scalarInnovation (scalarLastField z n p.1) (dt n) p.2 : ℝ) : ℂ) *
          Complex.I)) := by
      have hJ := measurable_scalarHistoryInnovationStep z (dt n) n
      exact (by fun_prop : Measurable _).stronglyMeasurable
    exact hm.integral_kernel_prod_right' (κ := scalarObservationStepKernel z (dt n) n)
  have hE : StronglyMeasurable E := by dsimp [E]; fun_prop
  have hiF : Integrable (fun h => E h * S h) (scalarObservationHistoryLaw z dt n) := by
    apply Integrable.of_bound (hE.mul hS).aestronglyMeasurable 1
    apply ae_of_all
    intro h
    change ‖E h * S h‖ ≤ 1
    rw [norm_mul]
    simp only [E, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact scalarInnovationChar_norm_le_one _ _ _
  have hiG : Integrable (fun h => G * E h) (scalarObservationHistoryLaw z dt n) :=
    (integrable_char_scalarHistoryWeightedInnovationSum z dt a n).const_mul G
  have he : scalarHistoryWeightedInnovationChar z dt a (n + 1) -
      G * scalarHistoryWeightedInnovationChar z dt a n =
      ∫ h, E h * S h - G * E h ∂scalarObservationHistoryLaw z dt n := by
    rw [integral_sub hiF hiG, integral_const_mul]
    rw [scalarHistoryWeightedInnovationChar_succ]
    rfl
  change ‖scalarHistoryWeightedInnovationChar z dt a (n + 1) -
    G * scalarHistoryWeightedInnovationChar z dt a n‖ ≤ _
  rw [he]
  have hbound : ∀ᵐ h ∂scalarObservationHistoryLaw z dt n,
      ‖E h * S h - G * E h‖ ≤
        (a n) ^ 2 * (dt n : ℝ) ^ 2 * Real.exp (2 * |a n| * dt n) := by
    apply ae_of_all
    intro h
    have hid : E h * S h - G * E h = E h * (S h - G) := by ring
    rw [hid, norm_mul]
    simp only [E, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact scalarInnovationChar_gaussian_error _ _ _
  exact (norm_integral_le_of_norm_le_const hbound).trans_eq (by simp)

lemma scalarHistoryWeightedInnovationChar_gaussian_error
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    ‖scalarHistoryWeightedInnovationChar z dt a n -
      Complex.exp (-((∑ k ∈ Finset.range n, (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ))‖ ≤
      ∑ k ∈ Finset.range n,
        (a k) ^ 2 * (dt k : ℝ) ^ 2 * Real.exp (2 * |a k| * dt k) := by
  induction n with
  | zero =>
    simp [scalarHistoryWeightedInnovationChar, scalarObservationHistoryLaw,
      scalarHistoryWeightedInnovationSum]
  | succ n ih =>
    let G : ℂ := Complex.exp (-(((dt n : ℝ) * (a n) ^ 2 / 2 : ℝ) : ℂ))
    let H : ℂ := Complex.exp (-((∑ k ∈ Finset.range n,
      (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ))
    have hG : ‖G‖ ≤ 1 := norm_exp_neg_ofReal_le_one _ (by positivity)
    have hnew : Complex.exp (-((∑ k ∈ Finset.range (n + 1),
        (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ)) = G * H := by
      dsimp [G, H]
      have hn : (a n) ^ 2 * (dt n : ℝ) / 2 = (dt n : ℝ) * (a n) ^ 2 / 2 := by ring
      rw [Finset.sum_range_succ, hn, Complex.ofReal_add, neg_add, Complex.exp_add]
      exact mul_comm _ _
    rw [hnew, Finset.sum_range_succ]
    calc
      _ = ‖(scalarHistoryWeightedInnovationChar z dt a (n + 1) -
          G * scalarHistoryWeightedInnovationChar z dt a n) +
        G * (scalarHistoryWeightedInnovationChar z dt a n - H)‖ := by congr 1; ring
      _ ≤ ‖scalarHistoryWeightedInnovationChar z dt a (n + 1) -
          G * scalarHistoryWeightedInnovationChar z dt a n‖ +
        ‖G * (scalarHistoryWeightedInnovationChar z dt a n - H)‖ := norm_add_le _ _
      _ ≤ (a n) ^ 2 * (dt n : ℝ) ^ 2 * Real.exp (2 * |a n| * dt n) +
        ∑ k ∈ Finset.range n,
          (a k) ^ 2 * (dt k : ℝ) ^ 2 * Real.exp (2 * |a k| * dt k) := by
        apply add_le_add (scalarHistoryWeightedInnovationChar_succ_error z dt a n)
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right hG (norm_nonneg _)).trans
          (by simpa only [H, one_mul] using ih)
      _ = _ := by ring

lemma scalarHistoryWeightedInnovationChar_eq_charFun
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) :
    scalarHistoryWeightedInnovationChar z dt a n =
      charFun ((scalarObservationHistoryLaw z dt n).map
        (scalarHistoryWeightedInnovationSum z dt a n)) 1 := by
  rw [charFun_apply_real, integral_map
    (measurable_scalarHistoryWeightedInnovationSum z dt a n).aemeasurable (by fun_prop)]
  simp only [Complex.ofReal_one, one_mul, scalarHistoryWeightedInnovationChar]

lemma scalarHistoryWeightedInnovationChar_mesh_error
    (z : ℝ) (dt : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ) (A h : ℝ)
    (hA : 0 ≤ A) (hh : h ≤ 1)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ h) (ha : ∀ k < n, |a k| ≤ A) :
    ‖scalarHistoryWeightedInnovationChar z dt a n -
      Complex.exp (-((∑ k ∈ Finset.range n, (a k) ^ 2 * (dt k : ℝ) / 2 : ℝ) : ℂ))‖ ≤
      Real.exp (2 * A) * h * ∑ k ∈ Finset.range n, (a k) ^ 2 * (dt k : ℝ) := by
  apply (scalarHistoryWeightedInnovationChar_gaussian_error z dt a n).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkN : k < n := Finset.mem_range.mp hk
  have ht : (dt k : ℝ) ≤ h := hdt k hkN
  have ht1 : (dt k : ℝ) ≤ 1 := ht.trans hh
  have hh0 : 0 ≤ h := (dt k).property.trans ht
  have hab : |a k| ≤ A := ha k hkN
  have hexp : 2 * |a k| * (dt k : ℝ) ≤ 2 * A := by
    calc
      _ ≤ 2 * A * (dt k : ℝ) := by gcongr
      _ ≤ 2 * A := by nlinarith
  have hsq : (dt k : ℝ) ^ 2 ≤ h * (dt k : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right ht (dt k).property]
  calc
    _ ≤ (a k) ^ 2 * (h * (dt k : ℝ)) * Real.exp (2 * A) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      · exact Real.exp_le_exp.mpr hexp
      · positivity
      · positivity
    _ = _ := by ring

lemma scalarHistoryWeightedInnovationChar_tendsto
    (z : ℕ → ℝ) (dt : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ)
    (A V : ℝ) (mesh : ℕ → ℝ) (hA : 0 ≤ A)
    (hbounds : ∀ᶠ j in Filter.atTop, mesh j ≤ 1 ∧
      (∀ k < N j, (dt j k : ℝ) ≤ mesh j) ∧ (∀ k < N j, |a j k| ≤ A))
    (hmesh : Filter.Tendsto mesh Filter.atTop (nhds 0))
    (hvar : Filter.Tendsto
      (fun j => ∑ k ∈ Finset.range (N j), (a j k) ^ 2 * (dt j k : ℝ))
        Filter.atTop (nhds V)) :
    Filter.Tendsto
      (fun j => scalarHistoryWeightedInnovationChar (z j) (dt j) (a j) (N j))
        Filter.atTop (nhds (Complex.exp (-((V / 2 : ℝ) : ℂ)))) := by
  let variance : ℕ → ℝ := fun j =>
    ∑ k ∈ Finset.range (N j), (a j k) ^ 2 * (dt j k : ℝ)
  let gaussian : ℕ → ℂ := fun j => Complex.exp (-((variance j / 2 : ℝ) : ℂ))
  have herr : ∀ᶠ j in Filter.atTop,
      ‖scalarHistoryWeightedInnovationChar (z j) (dt j) (a j) (N j) - gaussian j‖ ≤
        Real.exp (2 * A) * mesh j * variance j := by
    filter_upwards [hbounds] with j hj
    have h := scalarHistoryWeightedInnovationChar_mesh_error
      (z j) (dt j) (a j) (N j) A (mesh j) hA hj.1 hj.2.1 hj.2.2
    simpa only [gaussian, variance, Finset.sum_div] using h
  have hzero : Filter.Tendsto
      (fun j => scalarHistoryWeightedInnovationChar (z j) (dt j) (a j) (N j) - gaussian j)
        Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' herr
    have h := (hmesh.const_mul (Real.exp (2 * A))).mul hvar
    simpa only [mul_zero, zero_mul] using h
  have hGaussian : Filter.Tendsto gaussian Filter.atTop
      (nhds (Complex.exp (-((V / 2 : ℝ) : ℂ)))) := by
    dsimp [gaussian]
    have hReal := hvar.div_const 2
    have hComplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
    exact Complex.continuous_exp.continuousAt.tendsto.comp hComplex.neg
  have h := hzero.add hGaussian
  simpa only [zero_add, sub_add_cancel] using h

lemma integral_exp_imag_tendsto_of_ae_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => F n ω) Filter.atTop (nhds (f ω))) :
    Filter.Tendsto (fun n => ∫ ω, Complex.exp ((F n ω : ℂ) * Complex.I) ∂μ)
      Filter.atTop (nhds (∫ ω, Complex.exp ((f ω : ℂ) * Complex.I) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (Complex.measurable_exp.comp_aemeasurable
      ((Complex.continuous_ofReal.measurable.comp_aemeasurable (hF n)).mul_const Complex.I)).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    exact ae_of_all _ (fun ω => by simp only [Complex.norm_exp_ofReal_mul_I, le_refl])
  · filter_upwards [hlim] with ω hω
    exact Complex.continuous_exp.continuousAt.tendsto.comp (hω.ofReal.mul_const Complex.I)

lemma scalarHistoryWeightedInnovation_limit_characteristic
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (z : ℕ → ℝ) (dt : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ)
    (A V : ℝ) (mesh : ℕ → ℝ) (hA : 0 ≤ A)
    (hlaw : ∀ j, HasLaw (F j)
      ((scalarObservationHistoryLaw (z j) (dt j) (N j)).map
        (scalarHistoryWeightedInnovationSum (z j) (dt j) (a j) (N j))) μ)
    (hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun j => F j ω) Filter.atTop (nhds (f ω)))
    (hbounds : ∀ᶠ j in Filter.atTop, mesh j ≤ 1 ∧
      (∀ k < N j, (dt j k : ℝ) ≤ mesh j) ∧ (∀ k < N j, |a j k| ≤ A))
    (hmesh : Filter.Tendsto mesh Filter.atTop (nhds 0))
    (hvar : Filter.Tendsto
      (fun j => ∑ k ∈ Finset.range (N j), (a j k) ^ 2 * (dt j k : ℝ))
        Filter.atTop (nhds V)) :
    (∫ ω, Complex.exp ((f ω : ℂ) * Complex.I) ∂μ) =
      Complex.exp (-((V / 2 : ℝ) : ℂ)) := by
  have hfinite : ∀ j, (∫ ω, Complex.exp ((F j ω : ℂ) * Complex.I) ∂μ) =
      scalarHistoryWeightedInnovationChar (z j) (dt j) (a j) (N j) := by
    intro j
    calc
      _ = ∫ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
          ∂(scalarObservationHistoryLaw (z j) (dt j) (N j)).map
            (scalarHistoryWeightedInnovationSum (z j) (dt j) (a j) (N j)) := by
        simpa only [Function.comp_def] using (hlaw j).integral_comp
          (f := fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) (by fun_prop)
      _ = _ := by
        rw [integral_map
          (measurable_scalarHistoryWeightedInnovationSum (z j) (dt j) (a j) (N j)).aemeasurable
          (by fun_prop)]
        rfl
  have hfiniteLimit : Filter.Tendsto
      (fun j => ∫ ω, Complex.exp ((F j ω : ℂ) * Complex.I) ∂μ)
        Filter.atTop (nhds (Complex.exp (-((V / 2 : ℝ) : ℂ)))) := by
    simp_rw [hfinite]
    exact scalarHistoryWeightedInnovationChar_tendsto z dt a N A V mesh hA hbounds hmesh hvar
  have hactualLimit := integral_exp_imag_tendsto_of_ae_tendsto μ F f
    (fun j => (hlaw j).aemeasurable) hlim
  exact tendsto_nhds_unique hactualLimit hfiniteLimit

end SKConstants
