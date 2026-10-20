module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology

namespace SKConstants.Completion.LFine

theorem fine_entropy_exponent_margins (a f k : ℝ)
    (ha : 0 < a) (hk : k < a) (hkf : k < f) (hka : k < 1-a)
    (haf : a+f/2 < 1) :
    1-a < 1-k ∧ 1-f < 1-k ∧ a < 1-k ∧ a/2 < 1-k ∧
      2*a+f/2-1 < 1-k := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem eventually_log_power_mul_rpow_le (C p q : ℝ) (m : ℕ) (hpq : p < q) :
    ∀ᶠ n : ℕ in atTop, C*(Real.log (n : ℝ))^m*(n : ℝ)^p ≤ (n : ℝ)^q := by
  have ho := (isLittleO_log_rpow_rpow_atTop (m : ℝ) (sub_pos.mpr hpq)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb := ho.bound (c := (|C|+1)⁻¹) (by positivity)
  filter_upwards [hb,eventually_gt_atTop (1 : ℕ)] with n hn hn1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  simp only [Function.comp_def, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog m), abs_of_pos (Real.rpow_pos_of_pos hnR (q-p))] at hn
  have hc : C ≤ |C|+1 := by linarith [le_abs_self C]
  have hmul : C*(Real.log (n : ℝ))^m ≤ (n : ℝ)^(q-p) := by
    calc
      _ ≤ (|C|+1)*(Real.log (n : ℝ))^m :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg hlog m)
      _ ≤ (|C|+1)*((|C|+1)⁻¹*(n : ℝ)^(q-p)) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  calc
    _ ≤ (n : ℝ)^(q-p)*(n : ℝ)^p :=
      mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg hnR.le p)
    _ = _ := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem balanced_fine_entropy_margins (k : ℝ) (hk : k < 1/2) :
    1-(1/2 : ℝ) < 1-k ∧ 1-(1/2 : ℝ) < 1-k ∧
      (1/2 : ℝ) < 1-k ∧ (1/2 : ℝ)/2 < 1-k ∧
      2*(1/2 : ℝ)+(1/2 : ℝ)/2-1 < 1-k :=
  fine_entropy_exponent_margins (1/2) (1/2) k (by norm_num) hk hk (by linarith) (by norm_num)

end SKConstants.Completion.LFine
