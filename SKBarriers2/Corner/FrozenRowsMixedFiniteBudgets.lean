module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

@[expose] public section

noncomputable section
open scoped BigOperators

namespace SKBarriers2.Corner

def finiteMovingTestProfileBudget (Df Db : ℕ → ℝ) (A : ℕ → ℕ → ℝ) (Mc : ℝ) : ℝ :=
  1 + ∑ r : Fin 21, ∑ n : Fin 3,
    |(Df r.val + Db r.val * (max 1 Mc)^3) * A r.val (n.val+1)|

theorem one_le_finiteMovingTestProfileBudget (Df Db : ℕ → ℝ)
    (A : ℕ → ℕ → ℝ) (Mc : ℝ) : 1 ≤ finiteMovingTestProfileBudget Df Db A Mc := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

theorem movingTestProfileCoefficient_le_finiteBudget (Df Db : ℕ → ℝ)
    (A : ℕ → ℕ → ℝ) (Mc : ℝ) {r N : ℕ}
    (hr : r ≤ 20) (hN : 1 ≤ N) (hN3 : N ≤ 3) :
    (Df r + Db r * (max 1 Mc)^3) * A r N ≤ finiteMovingTestProfileBudget Df Db A Mc := by
  let ir : Fin 21 := ⟨r,Nat.lt_succ_of_le hr⟩
  let iN : Fin 3 := ⟨N-1,(Nat.sub_lt hN (Nat.zero_lt_succ 0)).trans_le hN3⟩
  have hiN : iN.val+1 = N := Nat.sub_add_cancel hN
  have hinner : |(Df ir.val + Db ir.val * (max 1 Mc)^3) * A ir.val (iN.val+1)| ≤
      ∑ n : Fin 3, |(Df ir.val + Db ir.val * (max 1 Mc)^3) * A ir.val (n.val+1)| :=
    Finset.single_le_sum
      (f := fun n : Fin 3 => |(Df ir.val + Db ir.val * (max 1 Mc)^3) * A ir.val (n.val+1)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ iN)
  have houter : (∑ n : Fin 3,
      |(Df ir.val + Db ir.val * (max 1 Mc)^3) * A ir.val (n.val+1)|) ≤
      ∑ j : Fin 21, ∑ n : Fin 3,
        |(Df j.val + Db j.val * (max 1 Mc)^3) * A j.val (n.val+1)| :=
    Finset.single_le_sum
      (f := fun j : Fin 21 => ∑ n : Fin 3,
        |(Df j.val + Db j.val * (max 1 Mc)^3) * A j.val (n.val+1)|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (Finset.mem_univ ir)
  have H := (le_abs_self ((Df ir.val + Db ir.val * (max 1 Mc)^3) *
    A ir.val (iN.val+1))).trans (hinner.trans houter)
  rw [hiN] at H
  exact H.trans (le_add_of_nonneg_left zero_le_one)

theorem exists_movingTestProfileFiniteBudget (Df Db : ℕ → ℝ)
    (A : ℕ → ℕ → ℝ) (Mc : ℝ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ r : ℕ, r ≤ 20 → ∀ N : ℕ, 1 ≤ N → N ≤ 3 →
      (Df r + Db r * (max 1 Mc)^3) * A r N ≤ D := by
  exact ⟨finiteMovingTestProfileBudget Df Db A Mc,
    one_le_finiteMovingTestProfileBudget Df Db A Mc,
    fun _ hr _ hN hN3 => movingTestProfileCoefficient_le_finiteBudget Df Db A Mc hr hN hN3⟩

theorem movingProfileCoefficient_weighted_le_of_le {T C D M W : ℝ} (N : ℕ)
    (hC : C ≤ D) (hT : 0 ≤ T) (hM : 0 ≤ M) (hW : 0 ≤ W) :
    (T*C)*M^N*W^(3*N) ≤ (T*D)*M^N*W^(3*N) :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hT) (pow_nonneg hM N))
    (pow_nonneg hW (3*N))

end SKBarriers2.Corner
