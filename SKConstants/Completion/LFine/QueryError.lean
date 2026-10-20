module

public import SKConstants.Completion.LFine.QueryGeometry
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace SKConstants.Completion.LFine
open GaussianProposal

theorem normalized_query_abs_sum_le (n : ℕ) (u : Fin n → ℝ)
    (hu : dot u u = (n : ℝ)) : (∑ i, |u i|) ≤ (n : ℝ) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (fun _ : Fin n => (1 : ℝ)) (fun i => |u i|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sq_abs] at hc
  have hsq : (∑ i, u i^2) = (n : ℝ) := by simpa only [dot, pow_two] using hu
  rw [hsq] at hc
  have hz : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  nlinarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]

theorem paperFrame_query_abs_sum_le {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    (∑ i, |normalizedQuery n (paperFrame E t 0) i|) ≤ (n : ℝ) := by
  apply normalized_query_abs_sum_le
  apply normalizedQuery_normSq _ (Nat.cast_nonneg n)
  simpa using paperFrame_orthogonal E t hE 0 0

theorem remainingProjection_trace {m n : ℕ}
    (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i=j then 1 else 0) :
    (∑ i, remainingProjection F i i) = (m : ℝ) := by
  simp only [remainingProjection, Matrix.mul_apply, Matrix.transpose_apply, tailRows]
  rw [Finset.sum_comm]
  have hrow (j : Fin m) : (∑ i, F j.succ i*F j.succ i) = 1 := by
    simpa only [dot, ite_true] using hF j.succ j.succ
  simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

theorem remainingProjection_trace_deficit {m n : ℕ}
    (F : Matrix (Fin (m+1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i=j then 1 else 0) :
    (∑ i, (1-remainingProjection F i i)) = (n : ℝ)-(m : ℝ) := by
  rw [Finset.sum_sub_distrib, remainingProjection_trace F hF]
  simp

theorem oneQuery_correction_abs_le {n : ℕ} (hn : 0 < n)
    (u m ζ : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (L s : ℝ)
    (hs : 0 ≤ s) (hL : 0 ≤ L)
    (hu : (∑ i, |u i|) ≤ (n : ℝ))
    (hP : ∀ i, |P i i| ≤ 1) (hm : ∀ i, |m i| ≤ 1)
    (hζ : ∀ i, |ζ i| ≤ L*s) :
    |2*((n : ℝ)⁻¹)^2*(∑ i, u i*P i i*m i*ζ i)| ≤ 2*L*s/(n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hterm (i : Fin n) : |u i*P i i*m i*ζ i| ≤ |u i| * (L*s) := by
    simp only [abs_mul]
    calc
      _ ≤ |u i| * 1*1*(L*s) := by gcongr; exact hP i; exact hm i; exact hζ i
      _ = _ := by ring
  have hsum : |∑ i, u i*P i i*m i*ζ i| ≤ (n : ℝ)*(L*s) := by
    calc
      _ ≤ ∑ i, |u i*P i i*m i*ζ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |u i| * (L*s) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (∑ i, |u i|)*(L*s) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hu (mul_nonneg hL hs)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*((n : ℝ)⁻¹)^2)]
  calc
    _ ≤ 2*((n : ℝ)⁻¹)^2*((n : ℝ)*(L*s)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

end SKConstants.Completion.LFine
