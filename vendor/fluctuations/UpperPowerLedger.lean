module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace OAI.SKFluctuations.PositiveLaplaceAssembly

open Filter
open scoped Topology

theorem tendsto_nat_log_pow_mul_rpow_neg (p : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ p * (n : ℝ) ^ (-κ))
      atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (p : ℝ) hκ).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [Real.rpow_natCast, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

theorem eventually_nat_rpow_mul_log_pow_le (p : ℕ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ a * (Real.log (n : ℝ)) ^ p ≤ (n : ℝ) ^ b := by
  have h := (tendsto_nat_log_pow_mul_rpow_neg p (sub_pos.mpr hab)).eventually
    (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1))
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hmul := mul_le_mul_of_nonneg_right hn.le
    (Real.rpow_nonneg (Nat.cast_nonneg n) b)
  calc
    (n : ℝ) ^ a * (Real.log (n : ℝ)) ^ p =
        ((Real.log (n : ℝ)) ^ p * (n : ℝ) ^ (-(b-a))) * (n : ℝ) ^ b := by
          rw [mul_assoc, ← Real.rpow_add hnpos]
          rw [show -(b-a)+b = a by ring]
          ring
    _ ≤ 1 * (n : ℝ) ^ b := hmul
    _ = _ := one_mul _

noncomputable def upperPressureLedger (m : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m) +
  (n : ℝ) ^ (-(5 : ℝ)/6 + 65*m + m/10000) * (Real.log (n : ℝ)) ^ 4 +
  (n : ℝ) ^ (-(5 : ℝ)/6 + 27*m + 20*(m/10000)) * Real.log (n : ℝ) +
  (n : ℝ) ^ (-(5 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)/6 + 5*m)

theorem eventually_upperPressureLedger_le {m : ℝ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      upperPressureLedger m n ≤ 4 * (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m) := by
  have hsecond := eventually_nat_rpow_mul_log_pow_le 4
    (show -(5 : ℝ)/6 + 65*m + m/10000 < -(5 : ℝ)/6 + 95*m by linarith)
  have hthird := eventually_nat_rpow_mul_log_pow_le 1
    (show -(5 : ℝ)/6 + 27*m + 20*(m/10000) < -(5 : ℝ)/6 + 95*m by linarith)
  have hlast := eventually_nat_rpow_mul_log_pow_le 0
    (show -(5 : ℝ) + (-(1 : ℝ)/6 + 5*m) < -(5 : ℝ)/6 + 95*m by linarith)
  filter_upwards [hsecond, hthird, hlast, eventually_ge_atTop (1 : ℕ)]
    with n hnsecond hnthird hnlast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnlast' : (n : ℝ) ^ (-(5 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)/6 + 5*m) ≤
      (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m) := by
    rw [← Real.rpow_add hnpos]
    simpa using hnlast
  simp only [pow_one] at hnthird
  unfold upperPressureLedger
  linarith

theorem eventually_upper_of_pressure_ledger (K pressureGap : ℕ → ℝ)
    {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (hidentity : ∀ᶠ n : ℕ in atTop,
      K n = (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ)/6 + 5*m) * pressureGap n)
    (hpressure : ∀ᶠ n : ℕ in atTop,
      pressureGap n ≤ C * upperPressureLedger m n) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ n : ℕ in atTop,
      K n ≤ C' * (n : ℝ) ^ (100*m) := by
  refine ⟨4*C+1, by linarith, ?_⟩
  filter_upwards [hidentity, hpressure, eventually_upperPressureLedger_le hm,
      eventually_ge_atTop (1 : ℕ)] with n hnidentity hnpressure hnledger hn1
  have hnpos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hgap : pressureGap n ≤ (4*C) * (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m) := by
    calc
      pressureGap n ≤ C * upperPressureLedger m n := hnpressure
      _ ≤ C * (4 * (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m)) :=
        mul_le_mul_of_nonneg_left hnledger hC
      _ = _ := by ring
  have hproduct :
      (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ)/6 + 5*m) *
          ((4*C) * (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m)) =
        (4*C) * (n : ℝ) ^ (100*m) := by
    calc
      _ = (4*C) * (((n : ℝ) ^ (1 : ℝ) *
          (n : ℝ) ^ (-(1 : ℝ)/6 + 5*m)) *
          (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m)) := by rw [Real.rpow_one]; ring
      _ = (4*C) * (n : ℝ) ^ ((1 : ℝ) + (-(1 : ℝ)/6 + 5*m) +
          (-(5 : ℝ)/6 + 95*m)) := by rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
      _ = _ := by congr 2; ring
  rw [hnidentity]
  calc
    _ ≤ (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ)/6 + 5*m) *
        ((4*C) * (n : ℝ) ^ (-(5 : ℝ)/6 + 95*m)) :=
      mul_le_mul_of_nonneg_left hgap
        (mul_nonneg hnpos.le (Real.rpow_nonneg hnpos.le _))
    _ = (4*C) * (n : ℝ) ^ (100*m) := hproduct
    _ ≤ (4*C+1) * (n : ℝ) ^ (100*m) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hnpos.le _)

end OAI.SKFluctuations.PositiveLaplaceAssembly
