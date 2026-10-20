module

public import WallClockScaleBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set

theorem wall_mean_suppression_of_calibration {T ε θ d rmin A C S K h : ℝ}
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Icc (0 : ℝ) 1)
    (_hd : 0 ≤ d) (hS : 0 ≤ S) (hr : rmin ≤ A*d)
    (hh : h ≤ d^2*rmin/4)
    (hK : K = h+(T-ε-θ*wallLowStrength T ε)*S)
    (hcal : |S-K/T| ≤ C*d^3) :
    S ≤ wallMeanScale (A/4+T*C) d ε := by
  have hT : 0 < T := hε.1.trans hε.2
  have hc0 := (wallLowStrength_bounds hε).1
  have htheta := mul_nonneg hθ.1 hc0
  have hupper := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcal) hT.le
  have heq : T*(S-K/T) = T*S-K := by field_simp [hT.ne']
  rw [heq] at hupper
  have hlow := mul_le_mul_of_nonneg_left hr (sq_nonneg d)
  have hmix := mul_nonneg htheta hS
  unfold wallMeanScale
  apply (le_div_iff₀ hε.1).mpr
  rw [hK] at hupper
  nlinarith

theorem wall_cubic_calibration_of_two_errors {S Γ K T d C₁ C₂ : ℝ}
    (h₁ : |S-Γ| ≤ C₁*d^3) (h₂ : |Γ-K/T| ≤ C₂*d^3) :
    |S-K/T| ≤ (C₁+C₂)*d^3 := by
  calc
    |S-K/T| = |(S-Γ)+(Γ-K/T)| := by congr 1; ring
    _ ≤ C₁*d^3+C₂*d^3 := (abs_add_le _ _).trans (add_le_add h₁ h₂)
    _ = (C₁+C₂)*d^3 := by ring

end OAI.SKFluctuations.LaplaceWindowFormalization
