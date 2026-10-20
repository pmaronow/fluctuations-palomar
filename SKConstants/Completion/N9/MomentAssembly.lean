module

public import SKConstants.Completion.LFine.ResidualEstimate
public import SKConstants.Completion.LFine.ScheduleSummation
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace SKConstants.Completion.N9
open LFine
variable {Ξ : Type*} [MeasurableSpace Ξ]

theorem integrable_residual_sqrt (μ : Measure Ξ) [IsFiniteMeasure μ]
    (Q Y : Ξ → ℝ) (hQi : Integrable Q μ) (hYi : Integrable Y μ)
    (hX : ∀ᵐ p ∂μ, 0 ≤ Q p-Y p) (hY : ∀ᵐ p ∂μ, 0 ≤ Y p) :
    Integrable (fun p => Real.sqrt (Q p-Y p)) μ := by
  apply ((hQi.add (integrable_const 1)).div_const 2).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (hQi.aestronglyMeasurable.sub hYi.aestronglyMeasurable))
  filter_upwards [hX,hY] with p hx hy
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt (Q p-Y p) ≤ (Q p+1)/2
  nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt (Q p-Y p)-1)]

theorem residual_sqrt_mean_le_one (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (Q Y : Ξ → ℝ) (hQi : Integrable Q μ)
    (hCi : Integrable (fun p => Real.sqrt (Q p-Y p)) μ)
    (hX : ∀ᵐ p ∂μ, 0 ≤ Q p-Y p) (hY : ∀ᵐ p ∂μ, 0 ≤ Y p)
    (hmean : (∫ p, Q p ∂μ) = 1) :
    (∫ p, Real.sqrt (Q p-Y p) ∂μ) ≤ 1 := by
  have hp : ∀ᵐ p ∂μ, Real.sqrt (Q p-Y p) ≤ (Q p+1)/2 := by
    filter_upwards [hX,hY] with p hx hy
    nlinarith [Real.sq_sqrt hx, sq_nonneg (Real.sqrt (Q p-Y p)-1)]
  have hi := integral_mono_ae hCi ((hQi.add (integrable_const 1)).div_const 2) hp
  rw [integral_div] at hi
  change (∫ p, Real.sqrt (Q p-Y p) ∂μ) ≤ (∫ p, Q p+1 ∂μ)/2 at hi
  rw [integral_add (f := fun p => Q p) (g := fun _ => 1) hQi (integrable_const 1), hmean] at hi
  simpa using hi

def fineQueryLowerIntegrand (N rank s L Q Y z : ℝ) : ℝ :=
  s*z*Real.sqrt (Q-Y) - L*s^2*Real.sqrt (Q-Y)*rank/N - 2*L*s/N

theorem expected_fineQueryLowerIntegrand (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (Q Y z : Ξ → ℝ) (N rank s L b B Ay Aq Ay₂ : ℝ)
    (hN : 0 < N) (hrank : 0 ≤ rank) (hs : 0 ≤ s) (hL : 0 ≤ L)
    (hX : ∀ᵐ p ∂μ, 0 ≤ Q p-Y p) (hY : ∀ᵐ p ∂μ, 0 ≤ Y p)
    (hz : ∀ᵐ p ∂μ, 0 ≤ z p ∧ z p ≤ L*s)
    (hQi : Integrable Q μ) (hYi : Integrable Y μ) (hzi : Integrable z μ)
    (hci : Integrable (fun p => z p*(Q p-1)) μ)
    (hqi : Integrable (fun p => (Q p-1)^2) μ)
    (hy₂i : Integrable (fun p => Y p^2) μ)
    (hCi : Integrable (fun p => Real.sqrt (Q p-Y p)) μ)
    (hEi : Integrable (fun p => s*z p*Real.sqrt (Q p-Y p)) μ)
    (hQmean : (∫ p, Q p ∂μ) = 1) (hzmean : (∫ p, z p ∂μ) = b)
    (hcov : -B ≤ ∫ p, z p*(Q p-1) ∂μ)
    (hEY : (∫ p, Y p ∂μ) ≤ Ay)
    (hEQ : (∫ p, (Q p-1)^2 ∂μ) ≤ Aq)
    (hEY₂ : (∫ p, Y p^2 ∂μ) ≤ Ay₂) :
    s*b - (s*B/2 + L*s^2/2*Ay + L*s^2*(Aq+Ay₂) +
      L*s^2*rank/N + 2*L*s/N) ≤
      ∫ p, fineQueryLowerIntegrand N rank s L (Q p) (Y p) (z p) ∂μ := by
  have hres := expected_weighted_residual_lower μ Q Y z s L b B Ay Aq Ay₂ hs hL hX hY hz
    hzi hci hYi hqi hy₂i hEi hzmean hcov hEY hEQ hEY₂
  have hC := residual_sqrt_mean_le_one μ Q Y hQi hCi hX hY hQmean
  have hcoef : 0 ≤ L*s^2*rank/N := by positivity
  have hdiag := mul_le_mul_of_nonneg_left hC hcoef
  have hdi : Integrable (fun p => L*s^2*Real.sqrt (Q p-Y p)*rank/N) μ := by
    convert hCi.const_mul (L*s^2*rank/N) using 1
    ext p
    ring
  unfold fineQueryLowerIntegrand
  rw [integral_sub (f := fun p => s*z p*Real.sqrt (Q p-Y p) -
      L*s^2*Real.sqrt (Q p-Y p)*rank/N) (g := fun _ => 2*L*s/N)
      (hEi.sub hdi) (integrable_const (2*L*s/N)),
    integral_sub (f := fun p => s*z p*Real.sqrt (Q p-Y p))
      (g := fun p => L*s^2*Real.sqrt (Q p-Y p)*rank/N) hEi hdi]
  have hdint : (∫ p, L*s^2*Real.sqrt (Q p-Y p)*rank/N ∂μ) =
      (L*s^2*rank/N)*(∫ p, Real.sqrt (Q p-Y p) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by ring)
  rw [hdint]
  simp only [integral_const, probReal_univ, one_smul]
  linarith

theorem fineQuery_moment_error_le (N : ℝ) (hN : 0 < N) (j : ℕ)
    (s h L M : ℝ) (hs : 0 < s) (hh : 0 ≤ h) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    s*(L*s/N)/2 + L*s^2/2*((j : ℝ)*h/(N*s^2)) +
      L*s^2*(M*h/(N*s^2) + 3*((j : ℝ)^2+j)*h^2/(N^2*s^4)) +
      L*s^2*j/N + 2*L*s/N ≤
    ((M+4)*L)*fineCellError N j s h := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hfirst : 0 ≤ (M+4)*((j : ℝ)+1) - ((j : ℝ)+1/2) := by
    nlinarith [mul_nonneg hM hj]
  have hsecond : 0 ≤ (M+4)*((j : ℝ)+1) - ((j : ℝ)/2+M) := by
    nlinarith [mul_nonneg hM hj]
  have hd1 := mul_nonneg (mul_nonneg hL hfirst) (sq_nonneg s)
  have hd2 := mul_nonneg (mul_nonneg hL hsecond) hh
  have hd3 := mul_nonneg (mul_nonneg hL (by linarith : 0 ≤ M+4-2)) hs.le
  have hd4 := mul_nonneg (mul_nonneg (mul_nonneg hL (by linarith : 0 ≤ M+4-3))
    (by positivity : 0 ≤ (j : ℝ)^2+j)) (sq_nonneg h)
  unfold fineCellError
  have hmain : 0 ≤ L*((M+4)*((j : ℝ)+1)-((j : ℝ)+1/2))*s^2 +
      L*((M+4)*((j : ℝ)+1)-((j : ℝ)/2+M))*h + L*(M+4-2)*s := by
    linarith
  have hb := add_nonneg (mul_nonneg hmain (mul_nonneg hN.le (sq_nonneg s))) hd4
  apply sub_nonneg.mp
  convert (div_nonneg hb (by positivity : 0 ≤ N^2*s^2)) using 1
  field_simp [hs.ne', hN.ne']
  ring

theorem expected_fineQueryLowerIntegrand_cell (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (Q Y z : Ξ → ℝ) (n j : ℕ) (hn : 0 < n) (s h L M b : ℝ)
    (hs : 0 < s) (hh : 0 ≤ h) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hX : ∀ᵐ p ∂μ, 0 ≤ Q p-Y p) (hY : ∀ᵐ p ∂μ, 0 ≤ Y p)
    (hz : ∀ᵐ p ∂μ, 0 ≤ z p ∧ z p ≤ L*s)
    (hQi : Integrable Q μ) (hYi : Integrable Y μ) (hzi : Integrable z μ)
    (hci : Integrable (fun p => z p*(Q p-1)) μ)
    (hqi : Integrable (fun p => (Q p-1)^2) μ)
    (hy₂i : Integrable (fun p => Y p^2) μ)
    (hCi : Integrable (fun p => Real.sqrt (Q p-Y p)) μ)
    (hEi : Integrable (fun p => s*z p*Real.sqrt (Q p-Y p)) μ)
    (hQmean : (∫ p, Q p ∂μ) = 1) (hzmean : (∫ p, z p ∂μ) = b)
    (hcov : -(L*s)/(n : ℝ) ≤ ∫ p, z p*(Q p-1) ∂μ)
    (hEY : (∫ p, Y p ∂μ) ≤ (j : ℝ)*h/((n : ℝ)*s^2))
    (hEQ : (∫ p, (Q p-1)^2 ∂μ) ≤ M*h/((n : ℝ)*s^2))
    (hEY₂ : (∫ p, Y p^2 ∂μ) ≤ 3*((j : ℝ)^2+j)*h^2/((n : ℝ)^2*s^4)) :
    s*b - ((M+4)*L)*fineCellError n j s h ≤
      ∫ p, fineQueryLowerIntegrand n j s L (Q p) (Y p) (z p) ∂μ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hres := expected_fineQueryLowerIntegrand μ Q Y z n j s L b (L*s/n)
    ((j : ℝ)*h/((n : ℝ)*s^2)) (M*h/((n : ℝ)*s^2))
    (3*((j : ℝ)^2+j)*h^2/((n : ℝ)^2*s^4)) hnR (Nat.cast_nonneg j) hs.le hL
    hX hY hz hQi hYi hzi hci hqi hy₂i hCi hEi hQmean hzmean
    (by simpa only [neg_div] using hcov) hEY hEQ hEY₂
  have herr := fineQuery_moment_error_le n hnR j s h L M hs hh hL hM
  linarith

end SKConstants.Completion.N9
