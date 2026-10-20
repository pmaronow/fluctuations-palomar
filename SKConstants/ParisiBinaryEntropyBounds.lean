module

public import SKConstants.ParisiBinaryEntropySeries

@[expose] public section

open Set Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport

lemma binaryEntropyPolynomial_zero (N : ℕ) : binaryEntropyPolynomial N 0=Real.log 2 := by
  unfold binaryEntropyPolynomial
  have H : (∑ k∈range N, (0:ℝ)^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ)))=0 := by
    apply sum_eq_zero
    intro k hk
    rw [zero_pow (by omega),zero_div]
  rw [H,sub_zero]

lemma reciprocal_successor_product_sum (N : ℕ) :
    (∑ k∈range N, 1/(((k+1:ℕ):ℝ)*((k+2:ℕ):ℝ)))=1-1/((N+1:ℕ):ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ,ih]
    push_cast
    have hN1 : (N:ℝ)+1≠0 := by positivity
    have hN2 : (N:ℝ)+2≠0 := by positivity
    field_simp
    ring

lemma binary_entropy_partial_sum_bounds (N : ℕ) {x : ℝ} (hx : |x|≤1) :
    0≤∑ k∈range N, x^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ)) ∧
    (∑ k∈range N, x^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ)))≤1 := by
  have hterm (k : ℕ) : 0≤x^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ)) := by
    apply div_nonneg
    · exact (show Even (2*k+2) from ⟨k+1,by omega⟩).pow_nonneg x
    · positivity
  refine ⟨sum_nonneg (fun k _ => hterm k),?_⟩
  calc
    _ ≤ ∑ k∈range N, 1/(((k+1:ℕ):ℝ)*((k+2:ℕ):ℝ)) := by
      apply sum_le_sum
      intro k hk
      have hpow : x^(2*k+2)≤1 := by
        have H := pow_le_pow_left₀ (abs_nonneg x) hx (2*k+2)
        exact (le_abs_self _).trans (by simpa only [abs_pow,one_pow] using H)
      have hden : ((k+1:ℕ):ℝ)*((k+2:ℕ):ℝ)≤((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α:=ℝ) k]
      exact (div_le_div_of_nonneg_right hpow (by positivity)).trans
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hden)
    _ = 1-1/((N+1:ℕ):ℝ) := reciprocal_successor_product_sum N
    _ ≤ 1 := by
      have H : 0≤1/((N+1:ℕ):ℝ) := by positivity
      linarith

theorem binaryEntropyPolynomial_abs_bound (N : ℕ) {x : ℝ} (hx : |x|≤1) :
    |binaryEntropyPolynomial N x|≤|Real.log 2|+1 := by
  have H := binary_entropy_partial_sum_bounds N hx
  unfold binaryEntropyPolynomial
  have HA := abs_sub_le (Real.log 2) 0 (∑ k∈range N, x^(2*k+2)/(((2*k+1:ℕ):ℝ)*((2*k+2:ℕ):ℝ)))
  simp only [sub_zero,zero_sub,abs_neg] at HA
  exact HA.trans (by rw [abs_of_nonneg H.1];exact add_le_add le_rfl H.2)

lemma binarySpinEntropy_bounds {x : ℝ} (hx : |x|≤1) :
    0≤binarySpinEntropy x ∧ binarySpinEntropy x≤Real.log 2 := by
  constructor
  · exact Real.binEntropy_nonneg (by linarith [(abs_le.mp hx).1]) (by linarith [(abs_le.mp hx).2])
  · exact Real.binEntropy_le_log_two

end SKConstants.ParisiFullSupport
