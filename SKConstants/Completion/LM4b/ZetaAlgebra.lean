module

public import SKConstants.CholeskyBarrier
public import SKConstants.Completion.LM4.All

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.Completion.LM4b

def rowPotential (x m : ℝ) : ℝ := x * m - m^2 / 2

def rowPrefixBefore {k : ℕ} (s T : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ i : Fin k, if i < j then s i * T i else 0

def rowPrefixAfter {k : ℕ} (s T : Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ i : Fin k, if i ≤ j then s i * T i else 0

theorem rowPrefixAfter_eq_before_add {k : ℕ} (s T : Fin k → ℝ) (j : Fin k) :
    rowPrefixAfter s T j = rowPrefixBefore s T j + s j * T j := by
  have he (i : Fin k) : (if i ≤ j then s i * T i else 0) =
      (if i < j then s i * T i else 0) + (if i = j then s i * T i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  simp only [rowPrefixAfter, rowPrefixBefore, he, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

def rowZeta {k : ℕ} (w s T g : Fin k → ℝ) (x e : ℝ) : ℝ :=
  (∑ j, w j * (rowPotential x (rowPrefixAfter s T j) -
    rowPotential x (rowPrefixBefore s T j))) +
    (∑ j, s j * (x - rowPrefixAfter s T j) * g j) - e / 2

def rowLinearEnergy {k : ℕ} (b s T g : Fin k → ℝ) (x e : ℝ) : ℝ :=
  x * (∑ j, b j * T j) + x * (∑ j, s j * g j) -
    (∑ i, s i * ∑ j, halfUpperTruncation (fun a b => T a * T b) i j * b j) -
    (∑ i, s i * ∑ j, fullUpperTruncation (fun a b => T a * g b) i j * s j) - e / 2

theorem halfUpper_row_pairing {k : ℕ} (s b T : Fin k → ℝ) :
    (∑ i, s i * ∑ j, halfUpperTruncation (fun a b => T a * T b) i j * b j) =
      ∑ j, b j * T j * (rowPrefixBefore s T j + s j * T j / 2) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [rowPrefixBefore, mul_add, Finset.mul_sum]
  have he (i : Fin k) : s i * (halfUpperTruncation (fun a b => T a * T b) i j * b j) =
      b j * T j * (if i < j then s i * T i else 0) +
        (if i = j then b j * T j * (s j * T j / 2) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [halfUpperTruncation, h, ite_true, ite_eq_right h.ne]
      ring
    · subst i
      simp only [halfUpperTruncation, lt_self_iff_false, ite_false, ite_true]
      ring
    · simp [halfUpperTruncation, not_lt.mpr h.le, h.ne']
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem fullUpper_row_pairing {k : ℕ} (s T g : Fin k → ℝ) :
    (∑ i, s i * ∑ j, fullUpperTruncation (fun a b => T a * g b) i j * s j) =
      ∑ j, s j * g j * rowPrefixAfter s T j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [rowPrefixAfter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i ≤ j <;> simp only [fullUpperTruncation, h, ite_true, ite_false] <;> ring

theorem rowLinearEnergy_eq_zeta {k : ℕ} (w b s T g : Fin k → ℝ)
    (x e : ℝ) (hb : ∀ j, b j = w j * s j) :
    rowLinearEnergy b s T g x e = rowZeta w s T g x e := by
  rw [rowLinearEnergy, halfUpper_row_pairing, fullUpper_row_pairing, rowZeta]
  simp_rw [Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [rowPrefixAfter_eq_before_add, hb j]
  unfold rowPotential
  ring

theorem rowPotential_abs_le {x m : ℝ} (hx : |x| ≤ 1) (hm : |m| ≤ 1) :
    |rowPotential x m| ≤ 3 / 2 := by
  have hxm : |x * m| ≤ 1 := (abs_mul x m).le.trans
    ((mul_le_mul hx hm (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hm2 : m^2 ≤ 1 := by nlinarith [sq_abs m, abs_nonneg m]
  calc
    _ ≤ |x * m| + |m^2 / 2| := abs_sub _ _
    _ ≤ 3 / 2 := by rw [abs_of_nonneg (by positivity : 0 ≤ m^2 / 2)]; linarith

end SKConstants.Completion.LM4b
