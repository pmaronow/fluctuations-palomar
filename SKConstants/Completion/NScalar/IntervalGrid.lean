module

public import SKConstants.BrownianDyadicGrid

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology

namespace SKConstants.Completion.NScalar
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def intervalClock (s t u : ℝ≥0) : ℝ≥0 :=
  s * min u 1 + (t - s) * (u - 1)

lemma intervalClock_monotone (s t : ℝ≥0) : Monotone (intervalClock s t) := by
  intro u v huv
  dsimp only [intervalClock]
  gcongr

def intervalDyadicGrid (s t : ℝ≥0) : ScalarDyadicNestedGrid where
  time l i := intervalClock s t ((brownianDyadicGrid 1).time l i)
  monotone l := (intervalClock_monotone s t).comp ((brownianDyadicGrid 1).monotone l)
  embed l d i := by rw [(brownianDyadicGrid 1).embed]
  zero l := by simp [intervalClock, (brownianDyadicGrid 1).zero]

lemma intervalDyadicGrid_first (s t : ℝ≥0) (l i : ℕ) (hi : i ≤ 2 ^ l) :
    (intervalDyadicGrid s t).time l i = (brownianDyadicGrid s).time l i := by
  have hr : ((i : ℝ≥0) / (2 : ℝ≥0)^l) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (show (i : ℝ≥0) ≤ (2 ^ l : ℕ) by exact_mod_cast hi)
  simp only [intervalDyadicGrid, intervalClock, brownianDyadicGrid, one_mul]
  rw [min_eq_left hr, tsub_eq_zero_of_le hr, mul_zero, add_zero, mul_div_assoc]

lemma intervalDyadicGrid_second (s t : ℝ≥0) (l i : ℕ) :
    (intervalDyadicGrid s t).time l (2 ^ l + i) =
      s + (t - s) * ((i : ℝ≥0) / (2 : ℝ≥0)^l) := by
  have hp : (2 : ℝ≥0)^l ≠ 0 := by positivity
  have hr : (1 : ℝ≥0) ≤ ((2^l + i : ℕ) : ℝ≥0) / (2 : ℝ≥0)^l := by
    apply (le_div_iff₀ (by positivity)).mpr
    simp only [one_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    exact le_add_of_nonneg_right (by positivity)
  simp only [intervalDyadicGrid, intervalClock, brownianDyadicGrid, one_mul]
  rw [min_eq_right hr, mul_one]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, add_div, div_self hp,
    add_tsub_cancel_left]

@[simp] lemma intervalDyadicGrid_start (s t : ℝ≥0) :
    (intervalDyadicGrid s t).time 0 1 = s := by
  rw [intervalDyadicGrid_first s t 0 1 (by norm_num), brownianDyadicGrid_horizon]

@[simp] lemma intervalDyadicGrid_end (s t : ℝ≥0) (hst : s ≤ t) :
    (intervalDyadicGrid s t).time 0 2 = t := by
  have H := intervalDyadicGrid_second s t 0 1
  simpa only [pow_zero, Nat.cast_one, div_one, mul_one, Nat.reduceAdd,
    add_tsub_cancel_of_le hst] using H

lemma intervalDyadicGrid_width_le (s t : ℝ≥0) (hst : s ≤ t) (l i : ℕ) :
    ((intervalDyadicGrid s t).time l (i+1) : ℝ) -
      (intervalDyadicGrid s t).time l i ≤ brownianDyadicWidth t l := by
  by_cases hi : i < 2^l
  · rw [intervalDyadicGrid_first s t l (i+1) (by omega),
      intervalDyadicGrid_first s t l i hi.le]
    exact (brownianDyadicGrid_width_le s l i).trans
      (div_le_div_of_nonneg_right (show (s : ℝ) ≤ t by exact_mod_cast hst) (by positivity))
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hi)
    rw [show 2^l + j + 1 = 2^l + (j+1) by omega,
      intervalDyadicGrid_second, intervalDyadicGrid_second]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
      NNReal.coe_ofNat, NNReal.coe_natCast, NNReal.coe_one, Nat.cast_add, Nat.cast_one,
      NNReal.coe_sub hst, brownianDyadicWidth]
    calc
      _ = ((t : ℝ) - s) / (2 : ℝ)^l := by ring
      _ ≤ (t : ℝ) / (2 : ℝ)^l :=
        div_le_div_of_nonneg_right (sub_le_self _ s.coe_nonneg) (by positivity)

end SKConstants.Completion.NScalar
