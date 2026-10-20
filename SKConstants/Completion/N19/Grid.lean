module

public import SKConstants.Completion.Blueprint.AssemblySequence
import Mathlib.Tactic

@[expose] public section
noncomputable section
open Filter
open scoped Topology

namespace SKConstants.Completion.N19
open Blueprint
set_option autoImplicit false

theorem gridAngle_step (p : Parameters) (n j : ℕ) :
    gridAngle p n (j + 1) - gridAngle p n j = Real.pi / (2 * gridSize p n) := by
  unfold gridAngle
  push_cast
  ring

theorem gridAngle_step_pos (p : Parameters) (n j : ℕ) :
    0 < gridAngle p n (j + 1) - gridAngle p n j := by
  rw [gridAngle_step]
  exact div_pos Real.pi_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (gridSize_pos p n)))

theorem gridAngle_gap_le (p : Parameters) (n j : ℕ) :
    |gridAngle p n (j + 1) - gridAngle p n j| ≤
      Real.exp (-((n : ℝ) ^ p.grid)) := by
  rw [abs_of_pos (gridAngle_step_pos p n j), gridAngle_step]
  have hm : (0 : ℝ) < gridSize p n := Nat.cast_pos.mpr (gridSize_pos p n)
  have hc : (Real.pi / 2) * Real.exp ((n : ℝ) ^ p.grid) ≤ gridSize p n :=
    Nat.le_ceil _
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * gridSize p n)).mpr
  have he := mul_le_mul_of_nonneg_right hc
    (Real.exp_pos (-((n : ℝ) ^ p.grid))).le
  have hex : Real.exp ((n : ℝ) ^ p.grid) * Real.exp (-((n : ℝ) ^ p.grid)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [mul_assoc, hex, mul_one] at he
  nlinarith

theorem amplification_log_le (a g C ε : ℝ) (hag : a < g) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ a * Real.log n ≤ ε * (n : ℝ) ^ g := by
  let d := (g - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hag' : a + d < g := by dsimp [d]; linarith
  filter_upwards [constant_rpow_le_small_rpow (a + d) g (C / d) ε hag'
    (div_nonneg hC hd.le) hε, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  calc
    C * (n : ℝ) ^ a * Real.log n ≤ C * (n : ℝ) ^ a * ((n : ℝ) ^ d / d) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hn0.le hd) (by positivity)
    _ = (C / d) * (n : ℝ) ^ (a + d) := by rw [Real.rpow_add hn0]; ring
    _ ≤ ε * (n : ℝ) ^ g := hn

theorem grid_amplification_le (p : Parameters) (C : ℝ) (hC : 0 ≤ C)
    (hag : p.a < p.grid) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      Real.exp (C * (n : ℝ) ^ p.a * Real.log n) *
        |gridAngle p n (j + 1) - gridAngle p n j| ≤
          Real.exp (-((n : ℝ) ^ p.grid) / 2) := by
  filter_upwards [amplification_log_le p.a p.grid C (1 / 2) hag hC (by norm_num)]
    with n hn j
  calc
    _ ≤ Real.exp (C * (n : ℝ) ^ p.a * Real.log n) *
        Real.exp (-((n : ℝ) ^ p.grid)) :=
      mul_le_mul_of_nonneg_left (gridAngle_gap_le p n j) (Real.exp_pos _).le
    _ = Real.exp (C * (n : ℝ) ^ p.a * Real.log n - (n : ℝ) ^ p.grid) := by
      rw [← Real.exp_add]; congr 1
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem quadratic_prefactor_absorption (C : ℝ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) ≤ Real.exp (-(n : ℝ) / 2) := by
  filter_upwards [amplification_log_le 0 1 2 (1 / 4) (by norm_num) (by norm_num)
      (by norm_num),
    constant_rpow_le_small_rpow 0 1 |Real.log C| (1 / 4) (by norm_num)
      (abs_nonneg _) (by norm_num), eventually_ge_atTop (1 : ℕ)] with n h1 h2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at h1 h2
  have he : Real.exp (Real.log C + 2 * Real.log n - n) =
      C * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hC,
      show (2 : ℝ) * Real.log n = (2 : ℕ) * Real.log n from rfl,
      Real.exp_nat_mul, Real.exp_log hn0]
  rw [← he]
  exact Real.exp_le_exp.mpr (by linarith [le_abs_self (Real.log C)])

end SKConstants.Completion.N19
