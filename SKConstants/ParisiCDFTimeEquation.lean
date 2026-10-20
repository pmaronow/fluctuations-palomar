module

public import SKConstants.ParisiCDFLeftPDE

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

lemma integral_eq_sub_of_hasDeriv_left_of_le {f d : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ q ∈ Ioo a b, HasDerivWithinAt f (d q) (Iio q) q)
    (hint : IntervalIntegrable d volume a b) :
    (∫ r in a..b, d r) = f b-f a := by
  have hi : IntervalIntegrable (fun r => -d (-r)) volume (-b) (-a) :=
    ((IntervalIntegrable.iff_comp_neg).mp hint).symm.neg
  have hc : ContinuousOn (fun r => f (-r)) (Icc (-b) (-a)) := by
    apply hcont.comp continuous_neg.continuousOn
    intro r hr
    exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hd : ∀ r ∈ Ioo (-b) (-a),
      HasDerivWithinAt (fun t => f (-t)) (-d (-r)) (Ioi r) r := by
    intro r hr
    have H := (hderiv (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩).comp r
      ((hasDerivAt_id r).neg.hasDerivWithinAt (s := Ioi r))
      (by intro t ht; exact neg_lt_neg ht)
    simpa only [Function.comp_def, mul_neg_one] using H
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (show -b ≤ -a by linarith) hc hd hi
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg,
    neg_neg, neg_neg] at H
  linarith

lemma scalarCDF_value_time_continuousOn (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (x : ℝ) :
    ContinuousOn (fun r => scalarCDFValue β α r (Real.toNNReal (1-r)) x) (Icc (0:ℝ) 1) := by
  intro q hq
  exact (scalarCDFValue_time_uniform β α ha h1 hq).tendsto_at x

lemma scalarCDF_gradient_time_continuousOn (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (x : ℝ) :
    ContinuousOn (fun r => scalarCDFGradient β α r (Real.toNNReal (1-r)) x) (Icc (0:ℝ) 1) := by
  intro q hq
  exact (scalarCDFGradient_time_uniform β α ha h1 hq).tendsto_at x

lemma scalarCDF_hessian_time_continuousOn (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (x : ℝ) :
    ContinuousOn (fun r => scalarCDFHessian β α r (Real.toNNReal (1-r)) x) (Icc (0:ℝ) 1) := by
  intro q hq
  exact (scalarCDFHessian_time_uniform β α ha h1 hq).tendsto_at x

def scalarCDFValueRate (β : ℝ) (α : ℝ → ℝ) (r x : ℝ) : ℝ :=
  -(β^2/2)*(scalarCDFHessian β α r (Real.toNNReal (1-r)) x +
    α r*(scalarCDFGradient β α r (Real.toNNReal (1-r)) x)^2)

def scalarCDFValueLeftRate (β : ℝ) (α : ℝ → ℝ) (r x : ℝ) : ℝ :=
  -(β^2/2)*(scalarCDFHessian β α r (Real.toNNReal (1-r)) x +
    Function.leftLim α r*(scalarCDFGradient β α r (Real.toNNReal (1-r)) x)^2)

lemma monotone_leftLim_ae_eq {α : ℝ → ℝ} (hα : Monotone α) :
    Function.leftLim α =ᵐ[volume] α := by
  filter_upwards [hα.countable_not_continuousAt.ae_notMem volume] with r hr
  exact (show ContinuousAt α r from not_not.mp hr).continuousWithinAt.leftLim_eq

lemma scalarCDFValueRate_intervalIntegrable (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) (x : ℝ) :
    IntervalIntegrable (fun r => scalarCDFValueRate β α r x) volume a b ∧
      IntervalIntegrable (fun r => scalarCDFValueLeftRate β α r x) volume a b := by
  have hsub : uIcc a b ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro r hr
    exact ⟨ha0.trans hr.1, hr.2.trans hb1⟩
  have hG := ((scalarCDF_gradient_time_continuousOn β α ha h1 x).mono hsub).pow 2
  have hH : IntervalIntegrable
      (fun r => scalarCDFHessian β α r (Real.toNNReal (1-r)) x) volume a b :=
    ((scalarCDF_hessian_time_continuousOn β α ha h1 x).mono hsub).intervalIntegrable
  constructor
  · exact (hH.add (α.mono.intervalIntegrable.mul_continuousOn hG)).const_mul (-(β^2/2))
  · exact (hH.add (α.mono.leftLim.intervalIntegrable.mul_continuousOn hG)).const_mul (-(β^2/2))

theorem scalarCDFValue_integral_time_equation (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) (x : ℝ) :
    scalarCDFValue β α b (Real.toNNReal (1-b)) x -
      scalarCDFValue β α a (Real.toNNReal (1-a)) x =
        ∫ r in a..b, scalarCDFValueRate β α r x := by
  have hsub : Icc a b ⊆ Icc (0:ℝ) 1 := by
    intro r hr
    exact ⟨ha0.trans hr.1, hr.2.trans hb1.le⟩
  have H := integral_eq_sub_of_hasDeriv_left_of_le hab
    ((scalarCDF_value_time_continuousOn β α ha h1 x).mono hsub)
    (fun r hr => scalarCDFValue_time_derivative_leftLimit β α ha h1 hβ
      (ha0.trans_lt hr.1) (hr.2.trans hb1) x)
    (scalarCDFValueRate_intervalIntegrable β α ha h1 ha0 hab hb1.le x).2
  rw [← H]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [monotone_leftLim_ae_eq α.mono] with r hr _
  simp only [scalarCDFValueLeftRate, scalarCDFValueRate, hr]

end SKConstants.ParisiFullSupport
