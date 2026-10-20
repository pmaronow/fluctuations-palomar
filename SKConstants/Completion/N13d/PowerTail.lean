module

public import SKConstants.Completion.N13d.Tail
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SKConstants.Completion.N13d
open GaussianProposal LC5

def sharpGaussianPower (a γ b z : ℝ) : ℝ :=
  max (2*z-a) (max (2*z-2*γ) (2*z-b))

theorem three_powers_le (N a γ b z : ℝ) (hN : 1 ≤ N) :
    N^(-a)+N^(-2*γ)+N^(-b) ≤ 3*N^(sharpGaussianPower a γ b z-2*z) := by
  have ha : -a ≤ sharpGaussianPower a γ b z-2*z := by
    have hh := le_max_left (2*z-a) (max (2*z-2*γ) (2*z-b))
    dsimp [sharpGaussianPower]
    linarith
  have hγ : -2*γ ≤ sharpGaussianPower a γ b z-2*z := by
    have hh := (le_max_left (2*z-2*γ) (2*z-b)).trans
      (le_max_right (2*z-a) (max (2*z-2*γ) (2*z-b)))
    dsimp [sharpGaussianPower]
    linarith
  have hb : -b ≤ sharpGaussianPower a γ b z-2*z := by
    have hh := (le_max_right (2*z-2*γ) (2*z-b)).trans
      (le_max_right (2*z-a) (max (2*z-2*γ) (2*z-b)))
    dsimp [sharpGaussianPower]
    linarith
  linarith [Real.rpow_le_rpow_of_exponent_le hN ha,
    Real.rpow_le_rpow_of_exponent_le hN hγ, Real.rpow_le_rpow_of_exponent_le hN hb]

theorem gaussian_power_ratio (N C ell a γ b z : ℝ) (hN : 0 < N)
    (hC : 0 < C) (hell : 0 < ell) :
    -(N^(-z))^2/(2*(3*C*ell*N^(sharpGaussianPower a γ b z-2*z-1))) =
      -N^(1-sharpGaussianPower a γ b z)/(6*C*ell) := by
  rw [← Real.rpow_mul_natCast hN.le, div_eq_div_iff]
  · norm_num only [Nat.cast_ofNat]
    have he : (-z)*2 = (1-sharpGaussianPower a γ b z)+
        (sharpGaussianPower a γ b z-2*z-1) := by ring
    rw [he, Real.rpow_add hN]
    ring
  · positivity
  · positivity

theorem completionEnergy_product_tail_C2 {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {n k : ℕ}
    (N : ℝ) (hN : 1 ≤ N) (c : U → Fin k → ℝ) (y : U → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y) (E : Set U) (hE : MeasurableSet E)
    (C ell a γ b z : ℝ) (hC : 0 < C) (hell : 0 < ell)
    (hvar : ∀ t ∈ E, completionVariance N (c t) (y t) ≤
      C*ell*N⁻¹*(N^(-a)+N^(-2*γ)+N^(-b))) :
    (μ.prod (completionNoiseLaw n k)).real
      {w | w.1 ∈ E ∧ N^(-z) ≤ |completionEnergy N (c w.1) (y w.1) w.2|} ≤
      2*Real.exp (-N^(1-sharpGaussianPower a γ b z)/(6*C*ell)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hbound (t : U) (ht : t ∈ E) : completionVariance N (c t) (y t) ≤
      3*C*ell*N^(sharpGaussianPower a γ b z-2*z-1) := by
    calc
      _ ≤ C*ell*N⁻¹*(N^(-a)+N^(-2*γ)+N^(-b)) := hvar t ht
      _ ≤ C*ell*N⁻¹*(3*N^(sharpGaussianPower a γ b z-2*z)) :=
        mul_le_mul_of_nonneg_left (three_powers_le N a γ b z hN) (by positivity)
      _ = _ := by
        rw [Real.rpow_sub hNpos (sharpGaussianPower a γ b z-2*z) 1, Real.rpow_one]
        ring
  have h := completionEnergy_product_tail_on μ N hNpos c y hc hy E hE
    (3*C*ell*N^(sharpGaussianPower a γ b z-2*z-1)) (N^(-z))
    (by positivity) (by positivity) hbound
  rwa [gaussian_power_ratio N C ell a γ b z hNpos hC hell] at h

end SKConstants.Completion.N13d
