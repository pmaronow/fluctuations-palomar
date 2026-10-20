module

public import SKConstants.Completion.LC5.CompletionLaws
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace SKConstants.Completion.N13d
open GaussianProposal LC5

theorem coefficient_sq_error_le {k : ℕ} (c s : EuclideanSpace ℝ (Fin k))
    (τ : ℝ) (hτ : 0 ≤ τ) (hclose : ‖c-s‖ ≤ τ) (j : Fin k) :
    (c j-s j)^2 ≤ τ^2 := by
  calc
    _ ≤ ∑ i : Fin k, (c i-s i)^2 :=
      Finset.single_le_sum (fun i _ => sq_nonneg (c i-s i)) (Finset.mem_univ j)
    _ = ‖c-s‖^2 := by rw [EuclideanSpace.real_norm_sq_eq]; rfl
    _ ≤ τ^2 := (sq_le_sq₀ (norm_nonneg _) hτ).mpr hclose

theorem coefficient_fourth_sum_le {k : ℕ} (c s : EuclideanSpace ℝ (Fin k))
    (M τ : ℝ) (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hc : ‖c‖ ≤ 1) (hclose : ‖c-s‖ ≤ τ) (hs : ∀ j, (s j)^2 ≤ M) :
    (∑ j, (c j)^4) ≤ 2*M+2*τ^2 := by
  have hcoord (j : Fin k) : (c j)^2 ≤ 2*M+2*τ^2 := by
    have he := coefficient_sq_error_le c s τ hτ hclose j
    nlinarith [hs j, sq_nonneg (s j-(c j-s j))]
  have hbudget : (∑ j, (c j)^2) ≤ 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg c]
  calc
    _ ≤ ∑ j, (2*M+2*τ^2)*(c j)^2 := by
      apply Finset.sum_le_sum
      intro j _
      nlinarith [mul_le_mul_of_nonneg_right (hcoord j) (sq_nonneg (c j))]
    _ = (2*M+2*τ^2)*(∑ j, (c j)^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2*M+2*τ^2)*1 := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := mul_one _

theorem residual_budget_le {k : ℕ} (c s : EuclideanSpace ℝ (Fin k))
    (τ p : ℝ) (hτ : 0 ≤ τ) (hp : 0 ≤ p) (hc : ‖c‖ ≤ 1)
    (hclose : ‖c-s‖ ≤ τ) (hs : ‖s‖^2 = 1-p) :
    (1-‖c‖^2)^2 ≤ 2*p^2+8*τ^2 := by
  have hs1 : ‖s‖ ≤ 1 := by nlinarith [norm_nonneg s]
  have hdiff : |‖s‖-‖c‖| ≤ τ := by
    calc
      _ ≤ ‖s-c‖ := abs_norm_sub_norm_le _ _
      _ = ‖c-s‖ := norm_sub_rev _ _
      _ ≤ τ := hclose
  have hsqdiff : |‖s‖^2-‖c‖^2| ≤ 2*τ := by
    calc
      _ = |‖s‖-‖c‖| * (‖s‖+‖c‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖s‖+‖c‖)]
        ring
      _ ≤ τ*2 := mul_le_mul hdiff (by linarith) (by positivity) hτ
      _ = _ := mul_comm _ _
  have hres0 : 0 ≤ 1-‖c‖^2 := by nlinarith [norm_nonneg c]
  have hres : 1-‖c‖^2 ≤ p+2*τ := by
    have ha := le_abs_self (‖s‖^2-‖c‖^2)
    linarith
  have hsq := (sq_le_sq₀ hres0 (by positivity : 0 ≤ p+2*τ)).mpr hres
  nlinarith [sq_nonneg (p-2*τ)]

theorem coefficientVariance_sharp_le {k : ℕ} (N : ℝ) (hN : 0 < N)
    (c s : EuclideanSpace ℝ (Fin k)) (M τ p : ℝ)
    (hM : 0 ≤ M) (hτ : 0 ≤ τ) (hp : 0 ≤ p)
    (hc : ‖c‖ ≤ 1) (hclose : ‖c-s‖ ≤ τ)
    (hscoord : ∀ j, (s j)^2 ≤ M) (hs : ‖s‖^2 = 1-p) :
    ((∑ j, (c j)^4)+(1-‖c‖^2)^2)/(2*N) ≤ N⁻¹*(M+5*τ^2+p^2) := by
  have hfour := coefficient_fourth_sum_le c s M τ hM hτ hc hclose hscoord
  have hres := residual_budget_le c s τ p hτ hp hc hclose hs
  apply (div_le_iff₀ (by positivity : 0 < 2*N)).mpr
  have hcancel : (N⁻¹*(M+5*τ^2+p^2))*(2*N) = 2*(M+5*τ^2+p^2) := by
    field_simp
  rw [hcancel]
  linarith

theorem completionVariance_sharp_le {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c s : EuclideanSpace ℝ (Fin k)) (y : Fin n → ℝ) (M τ p : ℝ)
    (hM : 0 ≤ M) (hτ : 0 ≤ τ) (hp : 0 ≤ p)
    (hc : ‖c‖ ≤ 1) (hclose : ‖c-s‖ ≤ τ)
    (hscoord : ∀ j, (s j)^2 ≤ M) (hs : ‖s‖^2 = 1-p)
    (hy : N⁻¹*dot y y = 1-∑ j, (c j)^2) :
    completionVariance N (fun j => c j) y ≤ N⁻¹*(M+5*τ^2+p^2) := by
  have hfour := coefficient_fourth_sum_le c s M τ hM hτ hc hclose hscoord
  have hres := residual_budget_le c s τ p hτ hp hc hclose hs
  have hsum : (∑ j, (c j)^2) = ‖c‖^2 := (EuclideanSpace.real_norm_sq_eq c).symm
  unfold completionVariance
  rw [hy, hsum]
  calc
    _ ≤ (1/2:ℝ)*N⁻¹*((2*M+2*τ^2)+(2*p^2+8*τ^2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfour hres) (by positivity)
    _ = _ := by ring

end SKConstants.Completion.N13d
