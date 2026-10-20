module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel

theorem exists_integer_bin_balance_of_cube {T tau z : ℝ}
    (hT : 0 ≤ T) (htau : 0 < tau) (hz : 0 ≤ z) (hcube : T=tau*z^3) :
    ∃k:ℕ,1 ≤ k ∧ (k:ℝ) ≤ z+2 ∧
      T/(k:ℝ)^2+((k:ℝ)+1)*tau ≤ 2*tau*z+3*tau := by
  let k := Nat.ceil z+1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hzk : z ≤ (k:ℝ) := by
    have h := Nat.le_ceil z
    dsimp only [k]
    push_cast
    linarith
  have hkz : (k:ℝ) ≤ z+2 := by
    have h := (Nat.ceil_lt_add_one hz).le
    dsimp only [k]
    push_cast
    linarith
  have hsq : z^2 ≤ (k:ℝ)^2 := by nlinarith
  have hterm : T/(k:ℝ)^2 ≤ tau*z := by
    apply (div_le_iff₀ (sq_pos_of_pos hk0)).2
    rw [hcube]
    calc
      tau*z^3=(tau*z)*z^2 := by ring
      _ ≤ (tau*z)*(k:ℝ)^2 := mul_le_mul_of_nonneg_left hsq (mul_nonneg htau.le hz)
  refine ⟨k,hk,hkz,?_⟩
  nlinarith

theorem exists_integer_bin_balance {T tau : ℝ} (hT : 0 ≤ T) (htau : 0 < tau) :
    ∃k:ℕ,1 ≤ k ∧ (k:ℝ) ≤ (T/tau)^((1:ℝ)/3)+2 ∧
      T/(k:ℝ)^2+((k:ℝ)+1)*tau ≤ 2*tau*(T/tau)^((1:ℝ)/3)+3*tau := by
  have hd : 0 ≤ T/tau := div_nonneg hT htau.le
  have hz : 0 ≤ (T/tau)^((1:ℝ)/3) := Real.rpow_nonneg hd _
  have hc : ((T/tau)^((1:ℝ)/3))^3=T/tau := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hd]
    norm_num
  apply exists_integer_bin_balance_of_cube hT htau hz
  rw [hc,mul_div_cancel₀ _ htau.ne']

theorem cubic_bin_balance_scale {y tau : ℝ} (hy : 0 ≤ y) (htau : 0 < tau) :
    tau*(y^2/tau)^((1:ℝ)/3)=y^((2:ℝ)/3)*tau^((2:ℝ)/3) := by
  rw [Real.div_rpow (sq_nonneg y) htau.le]
  have hyexp : (y^2)^((1:ℝ)/3)=y^((2:ℝ)/3) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hy]
    norm_num
  rw [hyexp]
  have htauexp : tau/tau^((1:ℝ)/3)=tau^((2:ℝ)/3) := by
    rw [show (2:ℝ)/3=1-(1:ℝ)/3 by norm_num,Real.rpow_sub htau,Real.rpow_one]
  calc
    tau*(y^((2:ℝ)/3)/tau^((1:ℝ)/3))=y^((2:ℝ)/3)*(tau/tau^((1:ℝ)/3)) := by ring
    _ = _ := by rw [htauexp]

theorem exists_integer_bin_balance_square {y tau : ℝ} (hy : 0 ≤ y) (htau : 0 < tau) :
    ∃k:ℕ,1 ≤ k ∧ (k:ℝ) ≤ (y^2/tau)^((1:ℝ)/3)+2 ∧
      (y/(k:ℝ))^2+((k:ℝ)+1)*tau ≤ 2*y^((2:ℝ)/3)*tau^((2:ℝ)/3)+3*tau := by
  obtain ⟨k,hk,hkscale,hbalance⟩ := exists_integer_bin_balance (sq_nonneg y) htau
  refine ⟨k,hk,hkscale,?_⟩
  rw [div_pow]
  have hscale := cubic_bin_balance_scale hy htau
  nlinarith

end OAI.SKFluctuations.WholeUnitSideKernel
