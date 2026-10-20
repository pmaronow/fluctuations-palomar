module

public import WallEndpointChord

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set

def wallMeanScale (A d ε : ℝ) : ℝ := A*d^3/ε

theorem wallLowStrength_pos {T ε : ℝ} (hε : ε ∈ Ioo 0 T) :
    0 < wallLowStrength T ε := by
  unfold wallLowStrength
  exact div_pos (lt_min hε.1 (sub_pos.mpr hε.2)) (by norm_num)

theorem wallMeanScale_nonneg {A d ε : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d) (hε : 0 < ε) :
    0 ≤ wallMeanScale A d ε := by unfold wallMeanScale; positivity

theorem wallLowRadius_le_wallMeanScale {A d rmin ε : ℝ}
    (_hA : 0 ≤ A) (_hd : 0 ≤ d) (hε : 0 < ε) (hr : rmin ≤ 2*A*d) :
    wallLowRadius d rmin ε ≤ wallMeanScale A d ε := by
  unfold wallLowRadius wallMeanScale
  have hh := mul_le_mul_of_nonneg_left hr (sq_nonneg d)
  apply (div_le_iff₀ (by positivity : 0 < 2*ε)).mpr
  have heq : A*d^3/ε*(2*ε) = 2*A*d^3 := by field_simp
  rw [heq]
  nlinarith

theorem wall_mean_radius_cost_le {T ε ε0 s A d rmin : ℝ}
    (hε : ε ∈ Ioo 0 T) (hε0 : 0 < ε0) (hεlower : ε0 ≤ ε)
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hd : 0 ≤ d) (hrmin : 0 ≤ rmin)
    (hr : rmin ≤ 2*A*d) :
    wallLowStrength T ε*s*((wallMeanScale A d ε)^2+(wallLowRadius d rmin ε)^2) ≤
      A^2*s*d^6/ε0 := by
  have hc := wallLowStrength_bounds hε
  have hr0 : 0 ≤ wallLowRadius d rmin ε :=
    div_nonneg (mul_nonneg (sq_nonneg d) hrmin) (by linarith [hε.1])
  have hmean := wallMeanScale_nonneg hA hd hε.1
  have hrad := wallLowRadius_le_wallMeanScale hA hd hε.1 hr
  have hsq : (wallLowRadius d rmin ε)^2 ≤ (wallMeanScale A d ε)^2 := by nlinarith
  have hfirst : wallLowStrength T ε*s*((wallMeanScale A d ε)^2+(wallLowRadius d rmin ε)^2) ≤
      ε*s*(wallMeanScale A d ε)^2 := by
    have hh := mul_le_mul_of_nonneg_left (by linarith [hsq] :
      (wallMeanScale A d ε)^2+(wallLowRadius d rmin ε)^2 ≤ 2*(wallMeanScale A d ε)^2)
      (mul_nonneg hc.1 hs)
    have hh' := mul_le_mul_of_nonneg_right hc.2.1 (mul_nonneg hs (sq_nonneg (wallMeanScale A d ε)))
    nlinarith
  have heq : ε*s*(wallMeanScale A d ε)^2 = A^2*s*d^6/ε := by
    unfold wallMeanScale
    field_simp [hε.1.ne']
  rw [heq] at hfirst
  exact hfirst.trans (div_le_div_of_nonneg_left (by positivity) hε0 hεlower)

theorem wallMeanScale_div_wallLowRadius {A d rmin ε : ℝ}
    (hd : 0 < d) (hrmin : 0 < rmin) (hε : 0 < ε) :
    wallMeanScale A d ε/wallLowRadius d rmin ε = 2*A*d/rmin := by
  unfold wallMeanScale wallLowRadius
  field_simp [hd.ne', hrmin.ne', hε.ne']

end OAI.SKFluctuations.LaplaceWindowFormalization
