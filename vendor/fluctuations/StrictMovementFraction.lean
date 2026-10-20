module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization

theorem strict_movement_fraction_of_scale {e D ey Dy omega C Ce Cd eta : ℝ}
    (he : 0 ≤ e) (hey : 0<ey) (hDy : 0<Dy) (hCd : 0<Cd)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (heta : 0 ≤ eta)
    (heupper : e ≤ Ce*ey) (hDlower : Cd*Dy ≤ D)
    (hw0 : 0 ≤ omega)
    (hwupper : omega ≤ C*eta*min 1 (Dy/ey))
    (hbudget : C*eta*(Ce+Cd)<Cd) :
    omega<D/(e+D) := by
  let a := C*eta
  have ha : 0 ≤ a := mul_nonneg hC heta
  have habudget : a*(Ce+Cd)<Cd := hbudget
  have ha1 : a<1 := by
    have hh : a*Cd ≤ a*(Ce+Cd) := mul_le_mul_of_nonneg_left (by linarith) ha
    have ht : a*Cd<1*Cd := by linarith
    nlinarith
  have hw1 : omega ≤ a := by
    exact hwupper.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Dy/ey)) ha)
  have hwDy : omega*ey ≤ a*Dy := by
    have hh : omega ≤ a*(Dy/ey) :=
      hwupper.trans (mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (Dy/ey)) ha)
    have hp := mul_le_mul_of_nonneg_right hh hey.le
    simpa only [div_eq_mul_inv,mul_assoc,inv_mul_cancel₀ hey.ne',mul_one] using hp
  have heprod : omega*e ≤ a*Ce*Dy := by
    have h1 := mul_le_mul_of_nonneg_left heupper hw0
    have h2 := mul_le_mul_of_nonneg_left hwDy hCe
    nlinarith
  have hD : 0<D := (mul_pos hCd hDy).trans_le hDlower
  have hrest : Cd*Dy*(1-a) ≤ D*(1-omega) := by
    have h1 := mul_le_mul_of_nonneg_right hDlower (by linarith : 0 ≤ 1-a)
    have h2 := mul_le_mul_of_nonneg_left (by linarith : 1-a ≤ 1-omega) hD.le
    exact h1.trans h2
  have hstrict : a*Ce*Dy<Cd*Dy*(1-a) := by
    have hh := mul_lt_mul_of_pos_right habudget hDy
    nlinarith
  have hprod : omega*(e+D)<D := by nlinarith
  exact (lt_div_iff₀ (by linarith : 0<e+D)).mpr hprod

end OAI.SKFluctuations.LaplaceWindowFormalization
