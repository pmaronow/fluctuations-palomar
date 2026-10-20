module

public import SKConstants.ScalarProcessTail
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace SKConstants

noncomputable def scalarGenerator (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  deriv (deriv f) y / (((2 : ℕ) : ℝ)) + Real.tanh y * deriv f y

theorem hasDerivAt_tanh_scalar (y : ℝ) :
    HasDerivAt Real.tanh (scalarDefect y) y := by
  have h := (Real.hasDerivAt_sinh y).fun_div (Real.hasDerivAt_cosh y)
    (Real.cosh_pos y).ne'
  have hfun : Real.tanh = (fun z ↦ Real.sinh z / Real.cosh z) :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [hfun]
  convert h using 1
  rw [scalarDefect_eq_inv_cosh_sq]
  have hc : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq y]

theorem hasDerivAt_scalarDefect (y : ℝ) :
    HasDerivAt scalarDefect (-2 * Real.tanh y * scalarDefect y) y := by
  have h := (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_tanh_scalar y).pow 2)
  convert h using 1
  · rfl
  · norm_num

theorem deriv_scalarDefect : deriv scalarDefect =
    (fun y ↦ -2 * Real.tanh y * scalarDefect y) := by
  funext y
  exact (hasDerivAt_scalarDefect y).deriv

theorem hasDerivAt_deriv_scalarDefect (y : ℝ) :
    HasDerivAt (deriv scalarDefect)
      (4 * scalarDefect y - 6 * (scalarDefect y) ^ 2) y := by
  rw [deriv_scalarDefect]
  have h := ((hasDerivAt_tanh_scalar y).const_mul (-2)).mul (hasDerivAt_scalarDefect y)
  convert h using 1
  unfold scalarDefect
  ring

theorem deriv_deriv_scalarDefect (y : ℝ) :
    deriv (deriv scalarDefect) y = 4 * scalarDefect y - 6 * (scalarDefect y) ^ 2 :=
  (hasDerivAt_deriv_scalarDefect y).deriv

theorem scalarGenerator_defect (y : ℝ) :
    scalarGenerator scalarDefect y = -(scalarDefect y) ^ 2 := by
  unfold scalarGenerator
  rw [deriv_deriv_scalarDefect, deriv_scalarDefect]
  norm_num only [Nat.cast_ofNat]
  unfold scalarDefect
  ring

theorem hasDerivAt_scalarDefect_sq (y : ℝ) :
    HasDerivAt (fun z ↦ (scalarDefect z) ^ 2)
      (-4 * Real.tanh y * (scalarDefect y) ^ 2) y := by
  convert (hasDerivAt_scalarDefect y).pow 2 using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

theorem deriv_scalarDefect_sq : deriv (fun z ↦ (scalarDefect z) ^ 2) =
    (fun y ↦ -4 * Real.tanh y * (scalarDefect y) ^ 2) := by
  funext y
  exact (hasDerivAt_scalarDefect_sq y).deriv

theorem hasDerivAt_deriv_scalarDefect_sq (y : ℝ) :
    HasDerivAt (deriv (fun z ↦ (scalarDefect z) ^ 2))
      (16 * (scalarDefect y) ^ 2 - 20 * (scalarDefect y) ^ 3) y := by
  rw [deriv_scalarDefect_sq]
  have h := ((hasDerivAt_tanh_scalar y).const_mul (-4)).mul (hasDerivAt_scalarDefect_sq y)
  convert h using 1
  unfold scalarDefect
  ring

theorem scalarGenerator_defect_sq (y : ℝ) :
    scalarGenerator (fun z ↦ (scalarDefect z) ^ 2) y =
      4 * (scalarDefect y) ^ 2 - 6 * (scalarDefect y) ^ 3 := by
  unfold scalarGenerator
  rw [(hasDerivAt_deriv_scalarDefect_sq y).deriv, deriv_scalarDefect_sq]
  norm_num only [Nat.cast_ofNat]
  unfold scalarDefect
  ring

end SKConstants
