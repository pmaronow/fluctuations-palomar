module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic

public section

namespace SKConstants

@[expose] noncomputable def binaryKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

theorem binaryKL_log_coverage (p q : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    p * Real.log (1 / q) ≤ binaryKL p q + Real.log 2 := by
  have hp' : 0 < 1 - p := sub_pos.mpr hp₁
  have hq' : 0 < 1 - q := sub_pos.mpr hq₁
  have hlog : Real.log (1 - q) ≤ 0 :=
    Real.log_nonpos (le_of_lt hq') (by linarith)
  have hneg : 0 ≤ -(1 - p) * Real.log (1 - q) := by
    nlinarith
  have hent := Real.binEntropy_le_log_two (p := p)
  unfold binaryKL
  rw [Real.log_div (ne_of_gt hp₀) (ne_of_gt hq₀),
    Real.log_div (ne_of_gt hp') (ne_of_gt hq'),
    Real.log_div one_ne_zero (ne_of_gt hq₀), Real.log_one]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog_def] at hent
  nlinarith

theorem binaryKL_exp_coverage (p q : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    Real.exp (-(binaryKL p q + Real.log 2) / p) ≤ q := by
  have h := binaryKL_log_coverage p q hp₀ hp₁ hq₀ hq₁
  rw [Real.log_div one_ne_zero (ne_of_gt hq₀), Real.log_one] at h
  have h' : -(binaryKL p q + Real.log 2) / p ≤ Real.log q := by
    apply (div_le_iff₀ hp₀).mpr
    nlinarith
  calc
    Real.exp (-(binaryKL p q + Real.log 2) / p)
        ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr h'
    _ = q := Real.exp_log hq₀

@[expose] noncomputable def finiteKL {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

theorem finite_log_sum {ι : Type*} (A : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ A, 0 < p i) (hq : ∀ i ∈ A, 0 < q i)
    (ha : 0 < ∑ i ∈ A, p i) (hb : 0 < ∑ i ∈ A, q i) :
    (∑ i ∈ A, p i) * Real.log ((∑ i ∈ A, p i) / (∑ i ∈ A, q i))
      ≤ ∑ i ∈ A, p i * Real.log (p i / q i) := by
  let a := ∑ i ∈ A, p i
  let b := ∑ i ∈ A, q i
  have hlocal : ∀ i ∈ A,
      p i * Real.log (a / b) - p i * Real.log (p i / q i)
        ≤ q i * a / b - p i := by
    intro i hi
    have hpi := hp i hi
    have hqi := hq i hi
    have ht : 0 < q i * a / (p i * b) := by positivity
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos ht) hpi.le
    have hc : p i * (q i * a / (p i * b) - 1) = q i * a / b - p i := by
      field_simp
    rw [hc] at h
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (ne_of_gt hqi) (ne_of_gt ha),
      Real.log_mul (ne_of_gt hpi) (ne_of_gt hb)] at h
    rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb),
      Real.log_div (ne_of_gt hpi) (ne_of_gt hqi)]
    nlinarith
  have hs := Finset.sum_le_sum hlocal
  have hs' : a * Real.log (a / b) - (∑ i ∈ A, p i * Real.log (p i / q i))
      ≤ b * a / b - a := by
    simpa only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_div, a, b] using hs
  have hz : b * a / b - a = 0 := by
    rw [mul_div_cancel_left₀ a (ne_of_gt hb)]
    ring
  rw [hz] at hs'
  exact sub_nonpos.mp hs'

theorem finiteKL_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    0 ≤ finiteKL p q := by
  have h := finite_log_sum Finset.univ p q (fun i _ ↦ hp i) (fun i _ ↦ hq i)
    (by rw [hp_sum]; norm_num) (by rw [hq_sum]; norm_num)
  simpa [hp_sum, hq_sum, finiteKL] using h

theorem finiteKL_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    binaryKL (∑ i ∈ A, p i) (∑ i ∈ A, q i) ≤ finiteKL p q := by
  have hpA := Finset.sum_pos (fun i (_ : i ∈ A) ↦ hp i) hA
  have hqA := Finset.sum_pos (fun i (_ : i ∈ A) ↦ hq i) hA
  have hpAc := Finset.sum_pos (fun i (_ : i ∈ Aᶜ) ↦ hp i) hAc
  have hqAc := Finset.sum_pos (fun i (_ : i ∈ Aᶜ) ↦ hq i) hAc
  have hp_decomp := Finset.sum_add_sum_compl A p
  have hq_decomp := Finset.sum_add_sum_compl A q
  rw [hp_sum] at hp_decomp
  rw [hq_sum] at hq_decomp
  have hp_comp : (∑ i ∈ Aᶜ, p i) = 1 - ∑ i ∈ A, p i := by linarith
  have hq_comp : (∑ i ∈ Aᶜ, q i) = 1 - ∑ i ∈ A, q i := by linarith
  have h₁ := finite_log_sum A p q (fun i _ ↦ hp i) (fun i _ ↦ hq i) hpA hqA
  have h₂ := finite_log_sum Aᶜ p q (fun i _ ↦ hp i) (fun i _ ↦ hq i) hpAc hqAc
  have h := add_le_add h₁ h₂
  rw [hp_comp, hq_comp] at h
  rw [Finset.sum_add_sum_compl] at h
  exact h

theorem finiteKL_exp_coverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (A : Finset ι)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hA : A.Nonempty) :
    Real.exp (-(finiteKL p q + Real.log 2) / (∑ i ∈ A, p i))
      ≤ ∑ i ∈ A, q i := by
  have hpA := Finset.sum_pos (fun i (_ : i ∈ A) ↦ hp i) hA
  have hqA := Finset.sum_pos (fun i (_ : i ∈ A) ↦ hq i) hA
  by_cases hAc : Aᶜ.Nonempty
  · have hpAc := Finset.sum_pos (fun i (_ : i ∈ Aᶜ) ↦ hp i) hAc
    have hqAc := Finset.sum_pos (fun i (_ : i ∈ Aᶜ) ↦ hq i) hAc
    have hp_decomp := Finset.sum_add_sum_compl A p
    have hq_decomp := Finset.sum_add_sum_compl A q
    rw [hp_sum] at hp_decomp
    rw [hq_sum] at hq_decomp
    have hpA_lt : (∑ i ∈ A, p i) < 1 := by linarith
    have hqA_lt : (∑ i ∈ A, q i) < 1 := by linarith
    have hpart := finiteKL_partition p q A hp hq hp_sum hq_sum hA hAc
    have h := (binaryKL_log_coverage _ _ hpA hpA_lt hqA hqA_lt).trans
      (add_le_add hpart (le_refl (Real.log 2)))
    rw [Real.log_div one_ne_zero (ne_of_gt hqA), Real.log_one] at h
    have h' : -(finiteKL p q + Real.log 2) / (∑ i ∈ A, p i)
        ≤ Real.log (∑ i ∈ A, q i) := by
      apply (div_le_iff₀ hpA).mpr
      nlinarith
    exact (Real.exp_le_exp.mpr h').trans_eq (Real.exp_log hqA)
  · have hAc_empty : Aᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAc
    have hq_decomp := Finset.sum_add_sum_compl A q
    rw [hAc_empty, Finset.sum_empty, add_zero, hq_sum] at hq_decomp
    rw [hq_decomp]
    apply Real.exp_le_one_iff.mpr
    have hKL := finiteKL_nonneg p q hp hq hp_sum hq_sum
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpA.le

theorem finiteKL_uniform_coverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (A : Finset ι) (K α : ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1)
    (hKL : finiteKL p q ≤ K) (hα : 0 < α) (hA_mass : α ≤ ∑ i ∈ A, p i) :
    Real.exp (-(K + Real.log 2) / α) ≤ ∑ i ∈ A, q i := by
  have hpA : 0 < ∑ i ∈ A, p i := hα.trans_le hA_mass
  have hA : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hpA
    exact lt_irrefl 0 hpA
  have hK : 0 ≤ K := (finiteKL_nonneg p q hp hq hp_sum hq_sum).trans hKL
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h₁ : -(K + Real.log 2) / α ≤ -(K + Real.log 2) / (∑ i ∈ A, p i) := by
    apply (div_le_div_iff₀ hα hpA).mpr
    nlinarith
  have h₂ : -(K + Real.log 2) / (∑ i ∈ A, p i)
      ≤ -(finiteKL p q + Real.log 2) / (∑ i ∈ A, p i) := by
    exact div_le_div_of_nonneg_right (by linarith) hpA.le
  exact (Real.exp_le_exp.mpr (h₁.trans h₂)).trans
    (finiteKL_exp_coverage p q A hp hq hp_sum hq_sum hA)

end SKConstants
