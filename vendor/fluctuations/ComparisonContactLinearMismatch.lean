module

public import ComparisonScalarWeightedCapTravel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal
set_option maxHeartbeats 2400000

theorem comparison_contact_linear_mismatch {g alpha S B : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hg : 0 < g r)
    (hp : comparisonLogSlope g r ∈ Icc (0 : ℝ) 1)
    (hS : 0 ≤ S (alpha r)) (hB : S (alpha r)^2 ≤ B (alpha r))
    (hG : radiusComparisonGradient g alpha S B r = 0) :
    |S (alpha r)-r| ≤ (B (alpha r)-S (alpha r)^2)/r := by
  have hSr := (comparison_gradient_nonneg_geometry hr hg hp hS hB hG.ge).1
  have hEq : 2*r*(r-S (alpha r)) = comparisonLogSlope g r*
      ((r-S (alpha r))^2+(B (alpha r)-S (alpha r)^2)) := by
    rw [comparison_gradient_slope hr.ne' hg.ne'] at hG
    have hh := (mul_eq_zero.mp hG).resolve_left hg.ne'
    have hh' := congrArg (fun x : ℝ => x*r) hh
    field_simp [hr.ne'] at hh'
    nlinarith [hh']
  have hz : 0 ≤ (r-S (alpha r))^2+(B (alpha r)-S (alpha r)^2) := by
    nlinarith [sq_nonneg (r-S (alpha r))]
  have hprod := mul_le_of_le_one_left hz hp.2
  have hquad := mul_nonneg hS (sub_nonneg.mpr hSr)
  rw [abs_of_nonpos (sub_nonpos.mpr hSr)]
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem comparison_laplace_contact_linear_mismatch {alpha S B : ℝ → ℝ}
    {d lam r : ℝ} (hd : d ≠ 0) (hlam : 0 < lam) (hr : 0 < r)
    (hS : 0 ≤ S (alpha r)) (hB : S (alpha r)^2 ≤ B (alpha r))
    (hG : radiusComparisonGradient (laplaceComparisonStrength d lam) alpha S B r = 0) :
    |S (alpha r)-r| ≤ (B (alpha r)-S (alpha r)^2)/r := by
  have hp := laplaceComparisonStrength_logSlope_mem hd hlam.ne' r
  exact comparison_contact_linear_mismatch hr (laplaceComparisonStrength_pos d hlam r)
    ⟨hp.1,hp.2.le⟩ hS hB hG

theorem comparison_weighted_linear_error_integral {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (e D err width radius : Ω → ℝ) {a : ℝ} (ha : 0 < a)
    (he : ∀ᵐ w ∂mu, 0 ≤ e w) (hD : ∀ᵐ w ∂mu, 0 ≤ D w)
    (hr : ∀ᵐ w ∂mu, a ≤ radius w)
    (hbound : ∀ᵐ w ∂mu, |err w| ≤ 4*width w+D w/radius w)
    (hi : Integrable (fun w => e w*|err w|) mu)
    (hwidth : Integrable (fun w => e w*width w) mu)
    (hthermal : Integrable (fun w => e w*D w) mu) :
    (∫w, e w*|err w| ∂mu) ≤
      4*(∫w, e w*width w ∂mu)+(∫w, e w*D w ∂mu)/a := by
  have hb : ∀ᵐ w ∂mu, e w*|err w| ≤ 4*(e w*width w)+(e w*D w)/a := by
    filter_upwards [he,hD,hr,hbound] with w hew hDw hrw hbw
    have hdiv := div_le_div_of_nonneg_left hDw ha hrw
    have hh := mul_le_mul_of_nonneg_left (hbw.trans (add_le_add le_rfl hdiv)) hew
    convert hh using 1
    ring
  have hj := (hwidth.const_mul 4).add (hthermal.div_const a)
  have hh := integral_mono_ae hi hj hb
  change (∫w, e w*|err w| ∂mu) ≤ ∫w, 4*(e w*width w)+(e w*D w)/a ∂mu at hh
  simpa only [integral_add (hwidth.const_mul 4) (hthermal.div_const a),
    integral_const_mul,integral_div] using hh

theorem comparison_contact_weighted_scaled_integral {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (e D err radius : Ω → ℝ) {c x : ℝ}
    (hc : 0 < c) (hx : 0 < x)
    (he : ∀ᵐ w ∂mu, 0 ≤ e w) (hD : ∀ᵐ w ∂mu, 0 ≤ D w)
    (hr : ∀ᵐ w ∂mu, c*x ≤ radius w)
    (hbound : ∀ᵐ w ∂mu, |err w| ≤ D w/radius w)
    (hi : Integrable (fun w => e w*|err w|) mu)
    (hthermal : Integrable (fun w => e w*D w) mu) :
    (∫w, e w*|err w| ∂mu)/x^4 ≤ (1/c)*((∫w, e w*D w ∂mu)/x^5) := by
  have hh := comparison_weighted_linear_error_integral mu e D err (fun _ => 0) radius
    (mul_pos hc hx) he hD hr (hbound.mono (by intro w hw; simpa using hw))
    hi (by simp) hthermal
  simp only [mul_zero,integral_zero,zero_add] at hh
  have hh' := div_le_div_of_nonneg_right hh (pow_pos hx 4).le
  convert hh' using 1
  field_simp

theorem comparison_contact_weighted_rate_tendsto
    {err thermal x : ℕ → ℝ} {c : ℝ} (_hc : 0 < c)
    (herr : ∀ᶠ n in atTop, 0 ≤ err n)
    (hx : ∀ᶠ n in atTop, 0 < x n)
    (hbound : ∀ᶠ n in atTop, err n/(x n)^4 ≤ (1/c)*(thermal n/(x n)^5))
    (hthermal : Tendsto (fun n => thermal n/(x n)^5) atTop (𝓝 0)) :
    Tendsto (fun n => err n/(x n)^4) atTop (𝓝 0) := by
  have hn : ∀ᶠ n in atTop, 0 ≤ err n/(x n)^4 := by
    filter_upwards [herr,hx] with n hn hxn
    exact div_nonneg hn (pow_pos hxn 4).le
  have ht := hthermal.const_mul (1/c)
  simp only [mul_zero] at ht
  exact squeeze_zero' hn hbound ht

end OAI.SKFluctuations.LaplaceWindowFormalization
