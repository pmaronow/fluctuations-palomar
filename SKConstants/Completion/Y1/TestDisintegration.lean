module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Set

namespace SKConstants.Completion.Y1
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem integral_past_indicator_mul (P : Measure A) (Q : Measure B) [SFinite P] [SFinite Q]
    (f : A × B → ℝ) (hi : Integrable f (P.prod Q)) (E : Set A) (hE : MeasurableSet E) :
    (∫ u, E.indicator (fun _ => (1 : ℝ)) u.1*f u ∂P.prod Q) =
      ∫ p in E, ∫ q, f (p,q) ∂Q ∂P := by
  have hEq : (fun u : A × B => E.indicator (fun _ => (1 : ℝ)) u.1*f u) =
      (Prod.fst ⁻¹' E).indicator f := by
    funext u
    by_cases hu : u.1 ∈ E <;> simp [hu]
  rw [hEq,integral_prod _ (hi.indicator (hE.preimage measurable_fst)),← integral_indicator hE]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  by_cases hp : p ∈ E <;> simp [hp]

theorem ae_fiber_power_le_of_weighted_tests
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (f : A × B → ℝ) (k : ℕ) (hk : k ≠ 0)
    (hi : Integrable (fun u => f u^k) (P.prod Q)) (C : ℝ)
    (htest : ∀ F : A → ℝ, Measurable F → (∀ p, |F p| ≤ 1) →
      (∫ u, (F u.1*f u)^k ∂P.prod Q) ≤ C*(∫ u, (F u.1)^2 ∂P.prod Q)) :
    ∀ᵐ p ∂P, (∫ q, f (p,q)^k ∂Q) ≤ C := by
  apply ae_le_of_forall_setIntegral_le hi.integral_prod_left (integrable_const C)
  intro E hE _
  let F : A → ℝ := E.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hE
  have hcap (p : A) : |F p| ≤ 1 := by by_cases hp : p ∈ E <;> simp [F,hp]
  have hp (u : A × B) : (F u.1*f u)^k = F u.1*f u^k := by
    by_cases hu : u.1 ∈ E <;> simp [F,hu,zero_pow hk]
  have hF2 : (fun p => F p^2) = F := by
    funext p
    by_cases hp : p ∈ E <;> simp [F,hp]
  have hright : (∫ u : A × B, F u.1^2 ∂P.prod Q) = ∫ p in E, (1 : ℝ) ∂P := by
    calc
      _ = ∫ p, F p^2 ∂P := by simpa using integral_fun_fst (μ := P) (ν := Q) (fun p => F p^2)
      _ = _ := by rw [hF2,integral_indicator hE]
  have h := htest F hF hcap
  simp_rw [hp] at h
  rw [integral_past_indicator_mul P Q _ hi E hE,hright] at h
  simpa only [← integral_const_mul,mul_one] using h

theorem ae_fiber_mean_zero_of_weighted_tests
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (f : A × B → ℝ) (hi : Integrable f (P.prod Q))
    (htest : ∀ F : A → ℝ, Measurable F → (∀ p, |F p| ≤ 1) →
      (∫ u, F u.1*f u ∂P.prod Q) = 0) :
    ∀ᵐ p ∂P, (∫ q, f (p,q) ∂Q) = 0 := by
  apply hi.integral_prod_left.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro E hE _
  rw [← integral_past_indicator_mul P Q f hi E hE]
  exact htest (E.indicator (fun _ => 1)) (measurable_const.indicator hE)
    (fun p => by by_cases hp : p ∈ E <;> simp [hp])

end SKConstants.Completion.Y1
