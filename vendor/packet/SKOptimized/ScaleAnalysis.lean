module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace SKOptimized

def criticalExponent : ℝ := ((2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)

def criticalSeparation (R : ℝ) (n : ℕ) : ℝ :=
  R * (n : ℝ) ^ (-criticalExponent)

theorem criticalExponent_pos : 0 < criticalExponent := by
  norm_num [criticalExponent]

theorem cubic_exponent_balance : 3 * criticalExponent = (2 : ℝ) / 3 := by
  norm_num [criticalExponent]

theorem cubic_exponent_constraint (κ : ℝ) :
    3 * κ ≤ (2 : ℝ) / 3 ↔ κ ≤ criticalExponent := by
  dsimp [criticalExponent]
  constructor <;> intro h <;> linarith

theorem critical_secondary_exponents :
    1 - 4 * criticalExponent = (1 : ℝ) / 9 ∧
    (23 : ℝ) / 15 - 6 * criticalExponent = (1 : ℝ) / 5 ∧
    1 - 3 * criticalExponent = (1 : ℝ) / 3 ∧
    criticalExponent < 1 - 3 * criticalExponent := by
  norm_num [criticalExponent]

theorem criticalSeparation_nonneg {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ criticalSeparation R n := by
  exact mul_nonneg hR (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem criticalSeparation_pos {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) :
    0 < criticalSeparation R n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  exact mul_pos hR (Real.rpow_pos_of_pos hn' _)

theorem criticalSeparation_pow (R : ℝ) (n m : ℕ) :
    criticalSeparation R n ^ m =
      R ^ m * (n : ℝ) ^ (-criticalExponent * (m : ℝ)) := by
  unfold criticalSeparation
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]

theorem criticalSeparation_cube (R : ℝ) (n : ℕ) :
    criticalSeparation R n ^ 3 = R ^ 3 * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
  rw [criticalSeparation_pow]
  norm_num [criticalExponent]

theorem critical_numerator_scale (R : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * criticalSeparation R n ^ 4 =
      R ^ 4 * (n : ℝ) ^ ((1 : ℝ) / 9) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [criticalSeparation_pow]
  calc
    (n : ℝ) * (R ^ 4 * (n : ℝ) ^ (-criticalExponent * (4 : ℝ))) =
        R ^ 4 * ((n : ℝ) ^ (1 : ℝ) *
          (n : ℝ) ^ (-criticalExponent * (4 : ℝ))) := by rw [Real.rpow_one]; ring
    _ = R ^ 4 * (n : ℝ) ^ ((1 : ℝ) / 9) := by
      rw [← Real.rpow_add hn']
      norm_num [criticalExponent]

theorem critical_denominator_scale (R : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ ((23 : ℝ) / 15) * criticalSeparation R n ^ 6 =
      R ^ 6 * (n : ℝ) ^ ((1 : ℝ) / 5) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [criticalSeparation_pow]
  calc
    (n : ℝ) ^ ((23 : ℝ) / 15) *
        (R ^ 6 * (n : ℝ) ^ (-criticalExponent * (6 : ℝ))) =
        R ^ 6 * ((n : ℝ) ^ ((23 : ℝ) / 15) *
          (n : ℝ) ^ (-criticalExponent * (6 : ℝ))) := by ring
    _ = R ^ 6 * (n : ℝ) ^ ((1 : ℝ) / 5) := by
      rw [← Real.rpow_add hn']
      norm_num [criticalExponent]

theorem critical_gibbs_scale (R : ℝ) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * criticalSeparation R n ^ 3 =
      R ^ 3 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [criticalSeparation_cube]
  calc
    (n : ℝ) * (R ^ 3 * (n : ℝ) ^ (-(2 : ℝ) / 3)) =
        R ^ 3 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(2 : ℝ) / 3)) := by
          rw [Real.rpow_one]; ring
    _ = R ^ 3 * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_add hn']
      norm_num

theorem cubic_gap_absorbs_mean_error {P p C g R : ℝ} {n : ℕ}
    (herror : P - p ≤ C * (n : ℝ) ^ (-(2 : ℝ) / 3))
    (hprefactor : 6 * C ≤ g * R ^ 3) :
    6 * (P - p) ≤ g * criticalSeparation R n ^ 3 := by
  rw [criticalSeparation_cube]
  have hpow : 0 ≤ (n : ℝ) ^ (-(2 : ℝ) / 3) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    6 * (P - p) ≤ 6 * (C * (n : ℝ) ^ (-(2 : ℝ) / 3)) := by linarith
    _ = (6 * C) * (n : ℝ) ^ (-(2 : ℝ) / 3) := by ring
    _ ≤ (g * R ^ 3) * (n : ℝ) ^ (-(2 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hprefactor hpow
    _ = g * (R ^ 3 * (n : ℝ) ^ (-(2 : ℝ) / 3)) := by ring

theorem restricted_gap_after_mean_error {restricted P p gap error : ℝ}
    (hrestricted : restricted ≤ 3 * P - gap)
    (herror : P - p ≤ error) (hbudget : 6 * error ≤ gap) :
    restricted ≤ 3 * p - gap / 2 := by
  linarith

theorem fifth_order_floor_absorption {ρ c C g : ℝ}
    (hρ : 0 ≤ ρ)
    (hbudget : C * c ^ 5 * ρ ^ 2 ≤ g / 4) :
    C * (c * ρ) ^ 5 ≤ g * ρ ^ 3 / 4 := by
  have hρ3 : 0 ≤ ρ ^ 3 := pow_nonneg hρ 3
  have h := mul_le_mul_of_nonneg_right hbudget hρ3
  calc
    C * (c * ρ) ^ 5 = (C * c ^ 5 * ρ ^ 2) * ρ ^ 3 := by ring
    _ ≤ (g / 4) * ρ ^ 3 := h
    _ = g * ρ ^ 3 / 4 := by ring

theorem eventually_power_mul_le {p q A B : ℝ} (hpq : p < q) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, B * (n : ℝ) ^ p ≤ A * (n : ℝ) ^ q := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (q - p)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hpq)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlim.eventually (eventually_ge_atTop (B / A)),
    eventually_gt_atTop (0 : ℕ)] with n hratio hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hB : B ≤ A * (n : ℝ) ^ (q - p) := by
    have h := (div_le_iff₀ hA).mp hratio
    simpa only [mul_comm] using h
  calc
    B * (n : ℝ) ^ p ≤
        (A * (n : ℝ) ^ (q - p)) * (n : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hn'.le _)
    _ = A * (n : ℝ) ^ q := by
      rw [mul_assoc, ← Real.rpow_add hn', sub_add_cancel]

theorem subcritical_horizon {κ A B : ℝ}
    (hκ : κ < criticalExponent) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (B * (n : ℝ) ^ κ) ≤
        Real.exp (A * (n : ℝ) ^ criticalExponent) := by
  filter_upwards [eventually_power_mul_le hκ hA (B := B)] with n hn
  exact Real.exp_le_exp.mpr hn

theorem polynomial_stretched_exponential_tendsto_zero (m a c : ℝ)
    (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ m *
      Real.exp (-c * (n : ℝ) ^ a)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m / a) c hc).comp hlim
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  change ((n : ℝ) ^ a) ^ (m / a) * Real.exp (-c * (n : ℝ) ^ a) = _
  rw [← Real.rpow_mul hn']
  have he : a * (m / a) = m := by field_simp [ha.ne']
  rw [he]

theorem exponential_bank_gibbs_decay {A c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      Real.exp (A * (n : ℝ) ^ criticalExponent -
        c * (n : ℝ) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n : ℕ in atTop,
      A * (n : ℝ) ^ criticalExponent ≤
        (c / 2) * (n : ℝ) ^ ((1 : ℝ) / 3) :=
    eventually_power_mul_le (by norm_num [criticalExponent]) (by linarith)
  have hzero : Tendsto (fun n : ℕ =>
      Real.exp (-(c / 2) * (n : ℝ) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      polynomial_stretched_exponential_tendsto_zero 0 ((1 : ℝ) / 3) (c / 2)
        (by norm_num) (by linarith)
  apply squeeze_zero' (Eventually.of_forall (fun n => (Real.exp_pos _).le)) ?_ hzero
  filter_upwards [hsmall] with n hn
  apply Real.exp_le_exp.mpr
  linarith

end SKOptimized
