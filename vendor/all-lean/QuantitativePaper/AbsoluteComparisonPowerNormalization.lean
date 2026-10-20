module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Exact cancellation of the temperature in the actual score-shell rates. -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 800000

theorem absolute_shell_power_normalization (A β u p z : ℝ)
    (hA : 0 < A) (hβ : 0 < β) (hu : 0 < u) (hexp : 1+2*p-z = 0) :
    β*(A*β^2)^p*(u/β)^z = A^p*u^z := by
  rw [Real.mul_rpow hA.le (sq_nonneg β),Real.div_rpow hu.le hβ.le]
  have hpow : β*(β^2)^p/(β^z) = 1 := by
    have hp : (β^2)^p = β^(2*p) := by rw [Real.rpow_mul hβ.le,Real.rpow_two]
    rw [hp]
    calc
      β*β^(2*p)/β^z = β^(1+2*p)/β^z := by rw [Real.rpow_add hβ,Real.rpow_one]
      _ = β^(1+2*p-z) := (Real.rpow_sub hβ (1+2*p) z).symm
      _ = 1 := by rw [hexp,Real.rpow_zero]
  calc
    β*(A^p*(β^2)^p)*(u^z/β^z) = (β*(β^2)^p/β^z)*(A^p*u^z) := by ring
    _ = _ := by rw [hpow,one_mul]

theorem absolute_shell_quarter_normalization (N β r u : ℝ)
    (hN : 0 < N) (hβ : 0 < β) (hr : 0 < r) (hu : 0 < u) :
    β*(N*(r*β^2))^(-3/4 : ℝ)*(u/β)^(-1/2 : ℝ) = (N*r)^(-3/4 : ℝ)*u^(-1/2 : ℝ) := by
  rw [show N*(r*β^2) = (N*r)*β^2 by ring]
  exact absolute_shell_power_normalization (N*r) β u (-3/4) (-1/2) (mul_pos hN hr) hβ hu (by norm_num)

theorem absolute_shell_third_normalization (N β r u : ℝ)
    (hN : 0 < N) (hβ : 0 < β) (hr : 0 < r) (hu : 0 < u) :
    β*(N*(r*β^2))^(-2/3 : ℝ)*(u/β)^(-1/3 : ℝ) = (N*r)^(-2/3 : ℝ)*u^(-1/3 : ℝ) := by
  rw [show N*(r*β^2) = (N*r)*β^2 by ring]
  exact absolute_shell_power_normalization (N*r) β u (-2/3) (-1/3) (mul_pos hN hr) hβ hu (by norm_num)

end QuantitativePaper
