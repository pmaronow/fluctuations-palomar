module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

namespace SKBarriers2

theorem small_power_absorbs_inverse_degree {ρ C M : ℝ} {n d e : ℕ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hne : n ≤ e) (hnd : n ≤ d) :
    ρ ^ e * (C / ρ) ^ n ≤ max 1 C ^ d * M ^ n := by
  have hfactor : ρ ^ e = ρ ^ (e - n) * ρ ^ n := by
    rw [← pow_add,Nat.sub_add_cancel hne]
  have heq : ρ ^ e * (C / ρ) ^ n = C ^ n * ρ ^ (e - n) := by
    rw [div_pow,hfactor]
    field_simp [ne_of_gt hρ]
  have hnorm : ρ ^ (e - n) ≤ 1 := pow_le_one₀ hρ.le hρ₁
  have hK : 1 ≤ max (1 : ℝ) C := le_max_left _ _
  have hCpow : C ^ n ≤ max 1 C ^ d :=
    (pow_le_pow_left₀ hC (le_max_right _ _) n).trans (pow_le_pow_right₀ hK hnd)
  rw [heq]
  calc
    C ^ n * ρ ^ (e - n) ≤ C ^ n :=
      mul_le_of_le_one_right (pow_nonneg hC _) hnorm
    _ ≤ max 1 C ^ d := hCpow
    _ ≤ max 1 C ^ d * M ^ n :=
      le_mul_of_one_le_right (pow_nonneg (le_trans (by norm_num) hK) _)
        (one_le_pow₀ hM)

theorem cube_mul_normalized_power_le {ρ C M : ℝ} {n : ℕ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hC : 0 ≤ C) (hM : 1 ≤ M) (hn : n ≤ 3) :
    ρ ^ 3 * (C / ρ) ^ n ≤ max 1 C ^ 3 * M ^ n :=
  small_power_absorbs_inverse_degree hρ hρ₁ hC hM hn hn

end SKBarriers2
