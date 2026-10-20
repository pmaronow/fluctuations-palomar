module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators

namespace SKConstants.Completion.LFine

theorem sqrt_lower_quadratic (x : ℝ) (hx : 0 ≤ x) :
    1 + (x-1)/2 - (x-1)^2/2 ≤ Real.sqrt x := by
  have hs := Real.sq_sqrt hx
  have hp := Real.sqrt_nonneg x
  have hf : 0 ≤ Real.sqrt x * (Real.sqrt x - 1)^2 * (Real.sqrt x + 2) := by positivity
  nlinarith

theorem sqrt_residual_lower (Q Y : ℝ) (hX : 0 ≤ Q-Y) :
    1 + (Q-1)/2 - Y/2 - (Q-1)^2 - Y^2 ≤ Real.sqrt (Q-Y) := by
  have h := sqrt_lower_quadratic (Q-Y) hX
  nlinarith [sq_nonneg (Q-1+Y)]

theorem weighted_residual_lower (Q Y z s L : ℝ)
    (hX : 0 ≤ Q-Y) (hY : 0 ≤ Y) (hs : 0 ≤ s) (hz : 0 ≤ z) (hzL : z ≤ L*s) :
    s*z + s/2*(z*(Q-1)) - L*s^2/2*Y - L*s^2*((Q-1)^2+Y^2) ≤
      s*z*Real.sqrt (Q-Y) := by
  have h := mul_le_mul_of_nonneg_left (sqrt_residual_lower Q Y hX) (mul_nonneg hs hz)
  have hL := mul_le_mul_of_nonneg_left hzL hs
  have h1 := mul_le_mul_of_nonneg_right hL hY
  have h2 := mul_le_mul_of_nonneg_right hL (add_nonneg (sq_nonneg (Q-1)) (sq_nonneg Y))
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

theorem expected_weighted_residual_lower (μ : Measure Ω)
    (Q Y z : Ω → ℝ) (s L b B Ay Aq Ay₂ : ℝ)
    (hs : 0 ≤ s) (hL : 0 ≤ L)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ Q ω - Y ω) (hY : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hz : ∀ᵐ ω ∂μ, 0 ≤ z ω ∧ z ω ≤ L*s)
    (hzi : Integrable z μ)
    (hci : Integrable (fun ω => z ω * (Q ω-1)) μ)
    (hYi : Integrable Y μ)
    (hqi : Integrable (fun ω => (Q ω-1)^2) μ)
    (hy₂i : Integrable (fun ω => Y ω^2) μ)
    (hEi : Integrable (fun ω => s*z ω*Real.sqrt (Q ω-Y ω)) μ)
    (hzmean : (∫ ω, z ω ∂μ) = b)
    (hcov : -B ≤ ∫ ω, z ω*(Q ω-1) ∂μ)
    (hEY : (∫ ω, Y ω ∂μ) ≤ Ay)
    (hEQ : (∫ ω, (Q ω-1)^2 ∂μ) ≤ Aq)
    (hEY₂ : (∫ ω, Y ω^2 ∂μ) ≤ Ay₂) :
    s*b - s*B/2 - L*s^2/2*Ay - L*s^2*(Aq+Ay₂) ≤
      ∫ ω, s*z ω*Real.sqrt (Q ω-Y ω) ∂μ := by
  have hleft : Integrable (fun ω =>
      s*z ω + s/2*(z ω*(Q ω-1)) - L*s^2/2*Y ω -
        L*s^2*((Q ω-1)^2+Y ω^2)) μ :=
    (((hzi.const_mul s).add (hci.const_mul (s/2))).sub
      (hYi.const_mul (L*s^2/2))).sub ((hqi.add hy₂i).const_mul (L*s^2))
  have hi := integral_mono_ae hleft hEi (by
    filter_upwards [hX,hY,hz] with ω hx hy hz
    exact weighted_residual_lower (Q ω) (Y ω) (z ω) s L hx hy hs hz.1 hz.2)
  rw [integral_sub (f := fun ω => s*z ω + s/2*(z ω*(Q ω-1)) - L*s^2/2*Y ω)
      (g := fun ω => L*s^2*((Q ω-1)^2+Y ω^2))
      (((hzi.const_mul s).add (hci.const_mul (s/2))).sub (hYi.const_mul (L*s^2/2)))
      ((hqi.add hy₂i).const_mul (L*s^2)),
    integral_sub (f := fun ω => s*z ω + s/2*(z ω*(Q ω-1)))
      (g := fun ω => L*s^2/2*Y ω)
      ((hzi.const_mul s).add (hci.const_mul (s/2))) (hYi.const_mul (L*s^2/2)),
    integral_add (f := fun ω => s*z ω) (g := fun ω => s/2*(z ω*(Q ω-1)))
      (hzi.const_mul s) (hci.const_mul (s/2)),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add (f := fun ω => (Q ω-1)^2) (g := fun ω => Y ω^2) hqi hy₂i, hzmean] at hi
  have hc := mul_le_mul_of_nonneg_left hcov hs
  have hy := mul_le_mul_of_nonneg_left hEY (mul_nonneg hL (sq_nonneg s))
  have hq := mul_le_mul_of_nonneg_left (add_le_add hEQ hEY₂)
    (mul_nonneg hL (sq_nonneg s))
  nlinarith

end SKConstants.Completion.LFine
