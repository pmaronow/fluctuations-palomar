module

public import SKConstants.Completion.LQ.GrowingMeshGeometry
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace SKConstants.Completion.LFine
open LQ

def fineCellError (N j s h : ℝ) : ℝ :=
  ((j+1)*s^2+s+(j+1)*h)/N + (j^2+j)*h^2/(N^2*s^2)

def fineScheduleError (N : ℝ) (K : ℕ) (V R : ℝ) : ℝ :=
  (((K : ℝ)+1)*(1+V)+Real.sqrt K)/N + ((K : ℝ)+1)^2*V*R/N^2

theorem sum_scales_le_sqrt (K : ℕ) (s : Fin K → ℝ)
    (hs : ∀ j, 0 ≤ s j) (hbudget : (∑ j, s j^2) ≤ 1) :
    (∑ j, s j) ≤ Real.sqrt K := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (fun _ : Fin K => (1 : ℝ)) s
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hm := mul_le_mul_of_nonneg_left hbudget hK
  have hz : 0 ≤ ∑ j, s j := Finset.sum_nonneg (fun j _ => hs j)
  nlinarith [Real.sqrt_nonneg (K : ℝ), Real.sq_sqrt hK]

theorem fineCellError_sum_le (N : ℝ) (hN : 0 < N) (K : ℕ)
    (s h : Fin K → ℝ) (V R : ℝ) (hR : 0 ≤ R)
    (hs : ∀ j, 0 < s j) (hh : ∀ j, 0 ≤ h j)
    (hsum : (∑ j, s j^2) ≤ 1) (hhsum : (∑ j, h j) ≤ V)
    (hscale : ∀ j, h j ≤ R*s j^2) :
    (∑ j, fineCellError N (j.val+1) (s j) (h j)) ≤ fineScheduleError N K V R := by
  have hcoef (j : Fin K) : (j.val+1 : ℝ)+1 ≤ (K : ℝ)+1 := by
    have hj : j.val+1 ≤ K := by omega
    exact_mod_cast Nat.succ_le_succ hj
  have hcoef₂ (j : Fin K) : (j.val+1 : ℝ)^2+(j.val+1 : ℝ) ≤ ((K : ℝ)+1)^2 := by
    have h1 := hcoef j
    have hj : 0 ≤ (j.val+1 : ℝ) := by positivity
    have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith
  have hfirst : (∑ j : Fin K,
      (((j.val+1 : ℝ)+1)*s j^2+s j+((j.val+1 : ℝ)+1)*h j)) ≤
        ((K : ℝ)+1)*(1+V)+Real.sqrt K := by
    calc
      _ ≤ ∑ j, (((K : ℝ)+1)*s j^2+s j+((K : ℝ)+1)*h j) :=
        Finset.sum_le_sum fun j _ => add_le_add
          (add_le_add (mul_le_mul_of_nonneg_right (hcoef j) (sq_nonneg _)) (le_refl (s j)))
          (mul_le_mul_of_nonneg_right (hcoef j) (hh j))
      _ = ((K : ℝ)+1)*(∑ j, s j^2)+(∑ j, s j)+((K : ℝ)+1)*(∑ j, h j) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (K : ℝ)+1 by positivity)
        have hv := mul_le_mul_of_nonneg_left hhsum (show 0 ≤ (K : ℝ)+1 by positivity)
        have hss := sum_scales_le_sqrt K s (fun j => (hs j).le) hsum
        nlinarith
  have hratio (j : Fin K) : (h j)^2/(s j)^2 ≤ R*h j := by
    apply (div_le_iff₀ (sq_pos_of_pos (hs j))).mpr
    nlinarith [mul_le_mul_of_nonneg_right (hscale j) (hh j)]
  have hsecond : (∑ j : Fin K,
      ((j.val+1 : ℝ)^2+(j.val+1 : ℝ))*h j^2/(s j)^2) ≤ ((K : ℝ)+1)^2*R*V := by
    calc
      _ ≤ ∑ j, ((K : ℝ)+1)^2*(R*h j) := Finset.sum_le_sum fun j _ => by
        calc
          _ = ((j.val+1 : ℝ)^2+(j.val+1 : ℝ))*(h j^2/(s j)^2) := by ring
          _ ≤ ((K : ℝ)+1)^2*(h j^2/(s j)^2) :=
            mul_le_mul_of_nonneg_right (hcoef₂ j) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left (hratio j) (sq_nonneg _)
      _ = ((K : ℝ)+1)^2*R*(∑ j, h j) := by simp only [← Finset.mul_sum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhsum (mul_nonneg (sq_nonneg _) hR)
  have heq : (∑ j, fineCellError N (j.val+1) (s j) (h j)) =
      (∑ j : Fin K, (((j.val+1 : ℝ)+1)*s j^2+s j+((j.val+1 : ℝ)+1)*h j))/N +
      (∑ j : Fin K, ((j.val+1 : ℝ)^2+(j.val+1 : ℝ))*h j^2/(s j)^2)/N^2 := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold fineCellError
    ring
  rw [heq]
  calc
    _ ≤ (((K : ℝ)+1)*(1+V)+Real.sqrt K)/N + (((K : ℝ)+1)^2*R*V)/N^2 :=
      add_le_add (div_le_div_of_nonneg_right hfirst hN.le)
        (div_le_div_of_nonneg_right hsecond (sq_nonneg N))
    _ = _ := by unfold fineScheduleError; ring

theorem growingCell_sqrt_ratio_le (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) (H : ℝ)
    (hsmall : meshDuration δ j ≤ H) :
    Real.sqrt (meshDuration δ (j+1)) / Real.sqrt (meshDuration δ j) ≤ Real.exp (H/8) := by
  rw [meshDuration_succ, Real.sqrt_mul (meshDuration_pos δ hδ j).le, ← Real.exp_half]
  have hs := (Real.sqrt_pos.mpr (meshDuration_pos δ hδ j)).ne'
  rw [mul_div_cancel_left₀ _ hs]
  exact Real.exp_le_exp.mpr (by linarith)

end SKConstants.Completion.LFine
