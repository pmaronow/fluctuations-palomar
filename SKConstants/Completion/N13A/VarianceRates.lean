module

public import SKConstants.Completion.N13A.Rates

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKConstants.Completion.N13A
open Blueprint

theorem variance_scale_le (N C a b w v : ℝ) (hN : 1 ≤ N) (hC : 0 ≤ C)
    (hv : v ≤ N^(-w)) :
    C/N * (N^(-a) + v + N^(-b)) ≤
      3*C*N^(-1-min a (min w b)) := by
  let m := min a (min w b)
  have ha : N^(-a) ≤ N^(-m) := Real.rpow_le_rpow_of_exponent_le hN (by dsimp [m]; linarith [min_le_left a (min w b)])
  have hw : N^(-w) ≤ N^(-m) := Real.rpow_le_rpow_of_exponent_le hN (by dsimp [m]; linarith [min_le_right a (min w b), min_le_left w b])
  have hb : N^(-b) ≤ N^(-m) := Real.rpow_le_rpow_of_exponent_le hN (by dsimp [m]; linarith [min_le_right a (min w b), min_le_right w b])
  have hN0 : 0 < N := by linarith
  have hp : N^(-1-m) = N^(-m)/N := by
    rw [show -1-m = -m-1 by ring, Real.rpow_sub hN0, Real.rpow_one]
  calc
    _ ≤ C/N * (3*N^(-m)) := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hC hN0.le)
    _ = _ := by rw [hp]; ring

theorem row_chernoff_exponent (N a z c : ℝ) (hN : 0<N) :
    c*N*(N^(-z))^2/N^(-a) = c*N^(1+a-2*z) := by
  have hs : (N^(-z))^2 = N^(-2*z) := by
    rw [← rpow_two_mul_eq N (-z) hN]
    congr 1
    ring
  calc
    _ = c * (N^(1:ℝ) * N^(-2*z) / N^(-a)) := by rw [Real.rpow_one, hs]; ring
    _ = _ := by
      rw [← Real.rpow_add hN, ← Real.rpow_sub hN]
      congr 2
      ring

theorem gaussian_chernoff_exponent (N C m z : ℝ) (hN : 0<N) (hC : 0<C) :
    (N^(-z))^2 / (2*(3*C*N^(-1-m))) = (1/(6*C))*N^(1+m-2*z) := by
  have hs : (N^(-z))^2 = N^(-2*z) := by
    rw [← rpow_two_mul_eq N (-z) hN]
    congr 1
    ring
  have he : N^(1+m-2*z) = N^(-2*z) / N^(-1-m) := by
    rw [← Real.rpow_sub hN]
    congr 1
    ring
  rw [hs, he]
  field_simp
  ring

theorem aemeasurable_information_of_observable {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (I L : A → ℝ) (N β : ℝ) (hN : N ≠ 0)
    (ho : AEMeasurable (fun y => I y/N - β*L y) μ) (hL : AEMeasurable L μ) :
    AEMeasurable I μ := by
  have h := (ho.add (hL.const_mul β)).const_mul N
  convert h using 1
  funext y
  change I y = N * (I y/N - β*L y + β*L y)
  field_simp [hN]
  ring

end SKConstants.Completion.N13A
