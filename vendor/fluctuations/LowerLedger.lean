module

public import Mathlib

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Filter
open scoped Topology

noncomputable section

def lowerEpsilon (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 3)

def lowerScale (m : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(1 : ℝ) / 6 + 5 * m)

def lowerError (m : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(5 : ℝ) / 6 + 7 * m)

def lowerDelta (m : ℝ) : ℝ := m / 10000

theorem lower_main_power {n : ℕ} (hn : 0 < (n : ℝ)) (m : ℝ) :
    lowerEpsilon n * (lowerScale m n) ^ 3 =
      (n : ℝ) ^ (-(5 : ℝ) / 6 + 15 * m) := by
  unfold lowerEpsilon lowerScale
  rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
  congr 1
  norm_num
  ring

theorem lower_error_power {n : ℕ} (hn : 0 < (n : ℝ)) (m : ℝ) :
    (n : ℝ) ^ (20 * lowerDelta m) * lowerError m n =
      (n : ℝ) ^ (-(5 : ℝ) / 6 + 7 * m + m / 500) := by
  unfold lowerDelta lowerError
  rw [← Real.rpow_add hn]
  congr 1
  ring

theorem lower_scaled_main_power {n : ℕ} (hn : 0 < (n : ℝ)) (m : ℝ) :
    (n : ℝ) * lowerScale m n *
      (lowerEpsilon n * (lowerScale m n) ^ 3) = (n : ℝ) ^ (20 * m) := by
  rw [lower_main_power hn m]
  unfold lowerScale
  calc
    (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 6 + 5 * m) *
        (n : ℝ) ^ (-(5 : ℝ) / 6 + 15 * m) =
        (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 6 + 5 * m) *
          (n : ℝ) ^ (-(5 : ℝ) / 6 + 15 * m) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) + (-(1 : ℝ) / 6 + 5 * m) +
        (-(5 : ℝ) / 6 + 15 * m)) := by
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    _ = (n : ℝ) ^ (20 * m) := by congr 1; ring

theorem eventually_coefficient_rpow_le {c d q r : ℝ}
    (hd : 0 < d) (hqr : q < r) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ q ≤ d * (n : ℝ) ^ r := by
  have hgrowth :=
    ((tendsto_rpow_atTop (sub_pos.mpr hqr)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
        (eventually_ge_atTop (c / d))
  filter_upwards [hgrowth, eventually_gt_atTop (0 : ℕ)] with n hg hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  change c / d ≤ (n : ℝ) ^ (r - q) at hg
  rw [Real.rpow_sub hnreal] at hg
  have hprod : (c / d) * (n : ℝ) ^ q ≤ (n : ℝ) ^ r :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hnreal q)).mp hg
  calc
    c * (n : ℝ) ^ q = d * ((c / d) * (n : ℝ) ^ q) := by
      field_simp [ne_of_gt hd]
    _ ≤ d * (n : ℝ) ^ r := mul_le_mul_of_nonneg_left hprod hd.le

theorem lower_error_exponent_lt {m : ℝ} (hm : 0 < m) :
    -(5 : ℝ) / 6 + 7 * m + m / 500 < -(5 : ℝ) / 6 + 15 * m := by
  linarith

theorem lower_error_eventually_absorbed {m a : ℝ} (b : ℝ)
    (hm : 0 < m) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop,
      b * (n : ℝ) ^ (20 * lowerDelta m) * lowerError m n ≤
        (a / 2) * lowerEpsilon n * (lowerScale m n) ^ 3 := by
  have hpow := eventually_coefficient_rpow_le
    (c := b) (d := a / 2)
    (q := -(5 : ℝ) / 6 + 7 * m + m / 500)
    (r := -(5 : ℝ) / 6 + 15 * m)
    (by positivity) (lower_error_exponent_lt hm)
  filter_upwards [hpow, eventually_gt_atTop (0 : ℕ)] with n hp hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    b * (n : ℝ) ^ (20 * lowerDelta m) * lowerError m n =
        b * ((n : ℝ) ^ (20 * lowerDelta m) * lowerError m n) := by ring
    _ = b * (n : ℝ) ^ (-(5 : ℝ) / 6 + 7 * m + m / 500) := by
      rw [lower_error_power hnreal m]
    _ ≤ (a / 2) * (n : ℝ) ^ (-(5 : ℝ) / 6 + 15 * m) := hp
    _ = (a / 2) * lowerEpsilon n * (lowerScale m n) ^ 3 := by
      rw [← lower_main_power hnreal m]
      ring

theorem lower_pressure_scaled_eventually
    (pressureDifference : ℕ → ℝ) {m a : ℝ} (b : ℝ)
    (hm : 0 < m) (ha : 0 < a)
    (hlower : ∀ᶠ n : ℕ in atTop,
      a * lowerEpsilon n * (lowerScale m n) ^ 3 -
        b * (n : ℝ) ^ (20 * lowerDelta m) * lowerError m n ≤
          pressureDifference n) :
    ∀ᶠ n : ℕ in atTop,
      (a / 2) * (n : ℝ) ^ (20 * m) ≤
        (n : ℝ) * lowerScale m n * pressureDifference n := by
  filter_upwards [hlower, lower_error_eventually_absorbed b hm ha,
    eventually_gt_atTop (0 : ℕ)] with n hp he hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < lowerScale m n := Real.rpow_pos_of_pos hnreal _
  have hhalf : (a / 2) * (lowerEpsilon n * (lowerScale m n) ^ 3) ≤
      pressureDifference n := by
    nlinarith [hp, he]
  have hscaled := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hnreal.le hs.le)
  calc
    (a / 2) * (n : ℝ) ^ (20 * m) =
        ((n : ℝ) * lowerScale m n) *
          ((a / 2) * (lowerEpsilon n * (lowerScale m n) ^ 3)) := by
      rw [← lower_scaled_main_power hnreal m]
      ring
    _ ≤ (n : ℝ) * lowerScale m n * pressureDifference n := hscaled

end

end OAI.SKFluctuations.LaplaceWindowFormalization
