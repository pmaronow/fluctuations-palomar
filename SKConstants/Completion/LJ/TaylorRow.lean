module

public import SKConstants.CholeskyBarrier
public import SKConstants.EuclideanMatrix
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace SKConstants.Completion.LJ

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def rowPotential (x m : ℝ) : ℝ := x * m - m ^ 2 / 2

def rowPair (s b : ι → ℝ) : ℝ := ∑ i, s i * b i

def rowOuter (v w : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * w j

def rowMatrixPair (s : ι → ℝ) (A : Matrix ι ι ℝ) (b : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, s i * A i j * b j

def rowPrevious (s T : ι → ℝ) (j : ι) : ℝ :=
  ∑ i, if i < j then s i * T i else 0

def rowCurrent (s T : ι → ℝ) (j : ι) : ℝ :=
  ∑ i, if i ≤ j then s i * T i else 0

theorem rowCurrent_eq (s T : ι → ℝ) (j : ι) :
    rowCurrent s T j = rowPrevious s T j + s j * T j := by
  classical
  have h (i : ι) : (if i ≤ j then s i * T i else 0) =
      (if i < j then s i * T i else 0) + (if i = j then s j * T j else 0) := by
    rcases lt_trichotomy i j with h | h | h <;> simp [h, le_of_lt, not_le_of_gt,
      not_lt_of_gt, ne_of_lt, ne_of_gt]
  simp only [rowCurrent, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, rowPrevious]

theorem row_half_triangle (s b T : ι → ℝ) :
    rowMatrixPair s (halfUpperTruncation (fun i j => T i * T j)) b =
      ∑ j, b j * (T j * rowPrevious s T j + s j * T j ^ 2 / 2) := by
  classical
  unfold rowMatrixPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h (i : ι) : s i * halfUpperTruncation (fun i j => T i * T j) i j * b j =
      b j * T j * (if i < j then s i * T i else 0) +
        (if i = j then b j * s j * T j ^ 2 / 2 else 0) := by
    by_cases hij : i < j
    · simp [halfUpperTruncation, hij, ne_of_lt hij]; ring
    · by_cases he : i = j
      · subst i; simp [halfUpperTruncation]; ring
      · simp [halfUpperTruncation, hij, he]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold rowPrevious
  ring

theorem row_full_triangle (s T g : ι → ℝ) :
    rowMatrixPair s (fullUpperTruncation (fun i j => T i * g j)) s =
      ∑ j, s j * g j * rowCurrent s T j := by
  classical
  unfold rowMatrixPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h (i : ι) : s i * fullUpperTruncation (fun i j => T i * g j) i j * s j =
      s j * g j * (if i ≤ j then s i * T i else 0) := by
    by_cases hij : i ≤ j
    · simp only [fullUpperTruncation, hij, ↓reduceIte]
      ring
    · simp [fullUpperTruncation, hij]
  simp only [h, ← Finset.mul_sum, rowCurrent]

def taylorRow (s b T g : ι → ℝ) (x : ℝ) : ℝ :=
  x * rowPair b T + x * rowPair s g -
    rowMatrixPair s (halfUpperTruncation (fun i j => T i * T j)) b -
    rowMatrixPair s (fullUpperTruncation (fun i j => T i * g j)) s - rowPair s b / 2

theorem taylorRow_eq (s b T g : ι → ℝ) (x : ℝ) (hs : ∀ j, s j ≠ 0) :
    taylorRow s b T g x =
      (∑ j, (b j / s j) *
        (rowPotential x (rowCurrent s T j) - rowPotential x (rowPrevious s T j))) +
      (∑ j, s j * (x - rowCurrent s T j) * g j) - rowPair s b / 2 := by
  rw [taylorRow, row_half_triangle, row_full_triangle]
  simp only [rowPair, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [rowCurrent_eq]
  unfold rowPotential
  field_simp [hs j]
  ring

theorem half_identity_pair (s b : ι → ℝ) :
    rowMatrixPair s (halfUpperTruncation (1 : Matrix ι ι ℝ)) b = rowPair s b / 2 := by
  classical
  unfold rowMatrixPair rowPair
  simp only [halfUpperTruncation, Matrix.one_apply, Nat.cast_ofNat]
  have h (i j : ι) : s i * (if i < j then (if i = j then (1 : ℝ) else 0)
      else if i = j then (if i = j then (1 : ℝ) else 0) / 2 else 0) * b j =
      if j = i then s i * b i / 2 else 0 := by
    rcases lt_trichotomy i j with h | h | h <;> simp [h, ne_of_lt, ne_of_gt, not_lt_of_gt]
    ring
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_div]

def energyFirstVariation (s b eq ev : ι → ℝ) (EA EH : Matrix ι ι ℝ) : ℝ :=
  rowPair eq b - rowMatrixPair s (halfUpperTruncation EA) b +
    rowPair s ev - rowMatrixPair s (fullUpperTruncation EH) s

theorem taylorRow_eq_firstVariation (s b T g : ι → ℝ) (x : ℝ) :
    taylorRow s b T g x = rowPair s b +
      energyFirstVariation s b (fun i => x * T i - s i) (fun i => x * g i - b i)
        (rowOuter T T - 1) (fun i j => T i * g j) := by
  classical
  have hhalf : halfUpperTruncation (rowOuter T T - 1) =
      halfUpperTruncation (fun i j => T i * T j) - halfUpperTruncation 1 := by
    ext i j
    simp only [halfUpperTruncation, Matrix.sub_apply, rowOuter]
    split_ifs <;> ring
  have hpair : rowMatrixPair s (halfUpperTruncation (rowOuter T T - 1)) b =
      rowMatrixPair s (halfUpperTruncation (fun i j => T i * T j)) b - rowPair s b / 2 := by
    rw [hhalf, ← half_identity_pair s b]
    simp only [rowMatrixPair, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hq : rowPair (fun i => x * T i - s i) b = x * rowPair b T - rowPair s b := by
    simp only [rowPair, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hv : rowPair s (fun i => x * g i - b i) = x * rowPair s g - rowPair s b := by
    simp only [rowPair, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold energyFirstVariation taylorRow
  rw [hpair, hq, hv]
  ring

theorem rowPrevious_increments {K : ℕ} (s : Fin K → ℝ) (a : ℕ → ℝ)
    (hs : ∀ i, s i ≠ 0) (j : Fin K) :
    rowPrevious s (fun i => (a (i + 1) - a i) / s i) j = a j - a 0 := by
  classical
  have he (i : Fin K) : s i * ((a (i + 1) - a i) / s i) = a (i + 1) - a i := by
    field_simp [hs i]
  unfold rowPrevious
  simp only [he, Fin.lt_def]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < (j : ℕ) then a (i + 1) - a i else 0) K]
  have hf : (Finset.range K).filter (fun i => i < (j : ℕ)) = Finset.range (j : ℕ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hf, Finset.sum_range_sub]

theorem rowCurrent_increments {K : ℕ} (s : Fin K → ℝ) (a : ℕ → ℝ)
    (hs : ∀ i, s i ≠ 0) (j : Fin K) :
    rowCurrent s (fun i => (a (i + 1) - a i) / s i) j = a (j + 1) - a 0 := by
  rw [rowCurrent_eq, rowPrevious_increments s a hs]
  have he : s j * ((a (j + 1) - a j) / s j) = a (j + 1) - a j := by field_simp [hs j]
  rw [he]
  ring

end SKConstants.Completion.LJ
