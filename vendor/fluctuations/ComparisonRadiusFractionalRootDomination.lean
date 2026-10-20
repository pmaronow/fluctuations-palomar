module

public import ComparisonRadiusFractionalIntegralAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open scoped BigOperators

theorem radius_fractional_root_le_endpoint_sum
    {f a b c : ℝ} (hf : 0 ≤ f) (ha : 0 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    f ^ b ≤ f ^ a + f ^ c := by
  by_cases hf1 : f ≤ 1
  · have h := Real.rpow_le_rpow_of_exponent_ge' hf hf1 ha hab
    exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg hf _))
  · have h1 : 1 ≤ f := le_of_lt (lt_of_not_ge hf1)
    have h := Real.rpow_le_rpow_of_exponent_le h1 hbc
    exact h.trans (le_add_of_nonneg_left (Real.rpow_nonneg hf _))

theorem radius_ordered_inverse_root_le_endpoint_sum
    {f : ℝ} (hf : 0 ≤ f) {q pmax : ℕ}
    (hq : 4 ≤ q) (hqp : q ≤ pmax) :
    f ^ ((q:ℝ)⁻¹) ≤ f ^ ((pmax:ℝ)⁻¹) + f ^ ((4:ℝ)⁻¹) := by
  have hqpos : (0:ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 4) hq)
  have hq4 : (4:ℝ) ≤ q := by exact_mod_cast hq
  have hqp' : (q:ℝ) ≤ pmax := by exact_mod_cast hqp
  exact radius_fractional_root_le_endpoint_sum hf (by positivity)
    (inv_anti₀ hqpos hqp') (inv_anti₀ (by norm_num) hq4)

theorem radius_frozen_level_root_le_initial_endpoint_sum
    {f : ℝ} (hf : 0 ≤ f) (depth j : ℕ) (hj : j < depth) :
    f ^ (((2*(j+2):ℕ):ℝ)⁻¹) ≤
      f ^ (((2*(depth+2):ℕ):ℝ)⁻¹) + f ^ ((4:ℝ)⁻¹) := by
  exact radius_ordered_inverse_root_le_endpoint_sum hf (by omega) (by omega)

theorem radius_fractional_roots_finset_le_endpoint
    {ι : Type*} (s : Finset ι) (exponent : ι → ℝ)
    {f a c : ℝ} (hf : 0 ≤ f) (ha : 0 ≤ a)
    (horders : ∀i∈s, a ≤ exponent i ∧ exponent i ≤ c) :
    (∑i∈s, f ^ exponent i) ≤ (s.card : ℝ)*(f ^ a + f ^ c) := by
  calc
    (∑i∈s, f ^ exponent i) ≤ ∑_i∈s, (f ^ a + f ^ c) := by
      apply Finset.sum_le_sum
      intro i hi
      exact radius_fractional_root_le_endpoint_sum hf ha (horders i hi).1
        (horders i hi).2
    _ = (s.card : ℝ)*(f ^ a + f ^ c) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_add]

theorem radius_bounded_linear_defect_le_fractional_envelope
    {f C q : ℝ} (hf : 0 ≤ f) (hC : 1 ≤ C) (hfC : f ≤ C)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    f ≤ C*(f ^ q + f ^ ((4:ℝ)⁻¹)) := by
  by_cases hf1 : f ≤ 1
  · have hpow : f ≤ f ^ q := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hf hf1 hq0.le hq1)
    have hsum : f ^ q ≤ f ^ q + f ^ ((4:ℝ)⁻¹) :=
      le_add_of_nonneg_right (Real.rpow_nonneg hf _)
    have hnonneg : 0 ≤ f ^ q + f ^ ((4:ℝ)⁻¹) := by positivity
    exact (hpow.trans hsum).trans (le_mul_of_one_le_left hnonneg hC)
  · have h1 : 1 ≤ f := le_of_lt (lt_of_not_ge hf1)
    have hpow : 1 ≤ f ^ ((4:ℝ)⁻¹) := Real.one_le_rpow h1 (by norm_num)
    have hCpow : C ≤ C*f ^ ((4:ℝ)⁻¹) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hC)
    have hsum : C*f ^ ((4:ℝ)⁻¹) ≤ C*(f ^ q + f ^ ((4:ℝ)⁻¹)) := by
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.rpow_nonneg hf _)) (zero_le_one.trans hC)
    exact hfC.trans (hCpow.trans hsum)

end OAI.SKFluctuations.LaplaceWindowFormalization
