module

public import SKConstants.Completion.J3B.DiscreteTaylor
public import SKConstants.ScalarProcessPosteriorIncrement

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.J3B
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem gaussianReal_centered_sixth (v : ℝ≥0) :
    (∫ y : ℝ, y ^ 6 ∂gaussianReal 0 v) = 15 * (v : ℝ) ^ 3 := by
  let q : ℝ := v
  let F : ℝ → ℝ := fun t => Real.exp (q * t ^ 2 / 2)
  have hF (t : ℝ) : HasDerivAt F (q * t * F t) t := by
    convert ((((hasDerivAt_id t).pow 2).const_mul q).div_const 2).exp using 1
    all_goals dsimp [F]
    all_goals ring
  have d1 : deriv F = fun t => q * t * F t := funext (fun t => (hF t).deriv)
  have d2 : deriv (fun t => q * t * F t) =
      fun t => (q + q ^ 2 * t ^ 2) * F t := by
    funext t
    convert (((hasDerivAt_id t).const_mul q).mul (hF t)).deriv using 1 <;> try rfl
    simp only [id_eq]
    ring
  have d3 : deriv (fun t => (q + q ^ 2 * t ^ 2) * F t) =
      fun t => (3 * q ^ 2 * t + q ^ 3 * t ^ 3) * F t := by
    funext t
    convert (((((hasDerivAt_id t).pow 2).const_mul (q ^ 2)).const_add q).mul
      (hF t)).deriv using 1 <;> try rfl
    simp only [Pi.pow_apply, id_eq]
    ring
  have d4 : deriv (fun t => (3 * q ^ 2 * t + q ^ 3 * t ^ 3) * F t) =
      fun t => (3 * q ^ 2 + 6 * q ^ 3 * t ^ 2 + q ^ 4 * t ^ 4) * F t := by
    funext t
    convert ((((hasDerivAt_id t).const_mul (3 * q ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul (q ^ 3))).mul (hF t)).deriv using 1 <;> try rfl
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  have d5 : deriv (fun t => (3 * q ^ 2 + 6 * q ^ 3 * t ^ 2 + q ^ 4 * t ^ 4) * F t) =
      fun t => (15 * q ^ 3 * t + 10 * q ^ 4 * t ^ 3 + q ^ 5 * t ^ 5) * F t := by
    funext t
    convert ((((((hasDerivAt_id t).pow 2).const_mul (6 * q ^ 3)).const_add
      (3 * q ^ 2)).add (((hasDerivAt_id t).pow 4).const_mul (q ^ 4))).mul
      (hF t)).deriv using 1 <;> try rfl
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  have d6 : deriv (fun t => (15 * q ^ 3 * t + 10 * q ^ 4 * t ^ 3 + q ^ 5 * t ^ 5) * F t) =
      fun t => (15 * q ^ 3 + 45 * q ^ 4 * t ^ 2 + 15 * q ^ 5 * t ^ 4 +
        q ^ 6 * t ^ 6) * F t := by
    funext t
    convert (((((hasDerivAt_id t).const_mul (15 * q ^ 3)).add
      (((hasDerivAt_id t).pow 3).const_mul (10 * q ^ 4))).add
      (((hasDerivAt_id t).pow 5).const_mul (q ^ 5))).mul (hF t)).deriv using 1 <;> try rfl
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    ring
  have hmoment := iteratedDeriv_mgf_zero (X := fun y : ℝ => y)
    (μ := gaussianReal 0 v) (by simp) 6
  simp only [Pi.pow_apply] at hmoment
  rw [← hmoment, mgf_fun_id_gaussianReal]
  simp only [zero_mul, zero_add]
  change iteratedDeriv 6 F 0 = _
  rw [iteratedDeriv_eq_iterate]
  change deriv (deriv (deriv (deriv (deriv (deriv F))))) 0 = _
  rw [d1, d2, d3, d4, d5, d6]
  simp [F, q]

theorem brownian_increment_sixth (W : BrownianSystem Ω) (s h : ℝ≥0) :
    Integrable (fun w => |W.B (s + h) w - W.B s w| ^ 6) W.law ∧
      (∫ w, |W.B (s + h) w - W.B s w| ^ 6 ∂W.law) = 15 * (h : ℝ) ^ 3 := by
  have hLaw := W.brownian.toIsPreBrownianReal.hasLaw_sub (s + h) s
  have hi := hLaw.integrable_fun_comp (gaussianReal_integrable_pow 0 _ 6)
  have he := hLaw.integral_comp (gaussianReal_integrable_pow 0 _ 6).aestronglyMeasurable
  have hab (x : ℝ) : |x| ^ 6 = x ^ 6 := by
    rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 6)]
  simp only [Function.comp_apply, Pi.sub_apply, gaussianReal_centered_sixth,
    coe_nndist, Real.dist_eq] at he
  change (∫ w, (W.B (s + h) w - W.B s w) ^ 6 ∂W.law) =
    15 * |((s + h : ℝ≥0) : ℝ) - (s : ℝ)| ^ 3 at he
  rw [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg] at he
  exact ⟨by simpa only [hab, Pi.sub_apply] using hi, by simpa only [hab] using he⟩

theorem boundedDrift_increment_sixth (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (s h : ℝ≥0) :
    Integrable (fun w => |b.solution W.driver (s + h) w -
      b.solution W.driver s w| ^ 6) W.law ∧
      (∫ w, |b.solution W.driver (s + h) w - b.solution W.driver s w| ^ 6 ∂W.law) ≤
        32 * (15 * (h : ℝ) ^ 3 + (b.bound : ℝ) ^ 6 * (h : ℝ) ^ 6) := by
  let := W.isProbability
  let X := fun w => W.B (s + h) w - W.B s w
  let Y := fun w => b.solution W.driver (s + h) w - b.solution W.driver s w
  have hb (w : Ω) : |b.displacement W s (s + h) w| ≤ (b.bound : ℝ) * h := by
    simpa only [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg]
      using b.displacement_bound W s (s + h) w
  have hXY : ∀ᵐ w ∂W.law,
      |Y w| ^ 6 ≤ 32 * (|X w| ^ 6 + ((b.bound : ℝ) * h) ^ 6) := by
    filter_upwards [b.solution_increment W s h] with w hw
    have he : Y w = X w + b.displacement W s (s + h) w := by dsimp [Y, X]; linarith
    rw [he]
    calc
      _ ≤ (|X w| + (b.bound : ℝ) * h) ^ 6 := by
        apply pow_le_pow_left₀ (abs_nonneg _)
        exact (abs_add_le _ _).trans (add_le_add le_rfl (hb w))
      _ ≤ _ := by
        have hp := add_pow_le (abs_nonneg (X w)) (mul_nonneg b.bound.coe_nonneg h.coe_nonneg) 6
        norm_num at hp
        exact hp
  have hiX := (brownian_increment_sixth W s h).1
  have hiB : Integrable (fun w => 32 * (|X w| ^ 6 + ((b.bound : ℝ) * h) ^ 6)) W.law :=
    (hiX.add (integrable_const _)).const_mul 32
  have hiY : Integrable (fun w => |Y w| ^ 6) W.law := hiB.mono'
    ((((b.solution_measurable W (s + h)).sub (b.solution_measurable W s)).abs.pow_const 6).aestronglyMeasurable)
    (hXY.mono (fun w hw => by simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hw))
  refine ⟨hiY, (integral_mono_ae hiY hiB hXY).trans_eq ?_⟩
  rw [integral_const_mul, integral_add hiX (integrable_const _),
    (brownian_increment_sixth W s h).2, integral_const, probReal_univ, one_smul]
  simp only [mul_pow]

theorem actualScalar_increment_sixth (W : BrownianSystem Ω) (β : ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Integrable (fun w => |actualParisiFullScalarProcess W β t w -
      actualParisiFullScalarProcess W β s w| ^ 6) W.law ∧
      (∫ w, |actualParisiFullScalarProcess W β t w -
        actualParisiFullScalarProcess W β s w| ^ 6 ∂W.law) ≤
        32 * (15 * ((t : ℝ) - s) ^ 3 + ((t : ℝ) - s) ^ 6) := by
  have h := boundedDrift_increment_sixth W (actualParisiFullScalarDrift β) s (t - s)
  simpa only [add_tsub_cancel_of_le hst, NNReal.coe_sub hst,
    actualParisiFullScalarDrift, ParisiFullSupport.finiteTemperatureCDFDrift,
    NNReal.coe_one, one_pow, one_mul, actualParisiFullScalarProcess] using h

end SKConstants.Completion.J3B
