module

/-
Adapted from OpenAI math, Apache-2.0, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/Probability/SKBarriers/Gaussian/ReciprocalSquares.lean
Changes: public module header and declarations added; import paths moved into SKConstants.Upstream; pinned Lean/Mathlib compatibility changes recorded in the port audit.
Upstream mathematical declarations retained; their namespace OAI is renamed SKConstantsOAI in this distribution.
-/

public import Mathlib

@[expose] public section

namespace SKConstantsOAI

section

section
noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem sum_nat_reciprocal_squares_aux (k : ℕ) :
    (∑ j : Fin k, 1/((j.val+1 : ℕ) : ℝ)^2) ≤ 2-2/((k+1 : ℕ) : ℝ) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    have hk : (0 : ℝ) < (k+1 : ℕ) := by positivity
    have hl : (0 : ℝ) < (k+1+1 : ℕ) := by positivity
    have hi : 1/((k+1 : ℕ) : ℝ)^2 ≤ 2/((k+1 : ℕ) : ℝ)-2/((k+1+1 : ℕ) : ℝ) := by
      apply (le_sub_iff_add_le).2
      field_simp [ne_of_gt hk,ne_of_gt hl]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    linarith

theorem sum_nat_reciprocal_squares (k : ℕ) :
    (∑ j : Fin k, 1/((j.val+1 : ℕ) : ℝ)^2) ≤ 2 :=
  (sum_nat_reciprocal_squares_aux k).trans (sub_le_self _ (by positivity))
end SK.Analytic

end
end

end

end SKConstantsOAI
