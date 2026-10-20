module

public import ChildMovementGain
public import HarmonicBarrierInterpolation

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set

theorem harmonicBarrierRadius_displacement {B t r v : ℝ}
    (hB : 0<B) (ht : t∈Icc (0:ℝ) 1) (hr : 0 ≤ r) (hv : 0 ≤ v) :
    r-harmonicBarrierRadius B t r v=
      t*(r+B)*(r-v)/((1-t)*(v+B)+t*(r+B)) := by
  have hR : r+B≠0 := (by linarith : 0<r+B).ne'
  have hV : v+B≠0 := (by linarith : 0<v+B).ne'
  have hden := (harmonicBarrierDenominator_pos hB ht hr hv).ne'
  have hnew : 0<(1-t)*(v+B)+t*(r+B) := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [←h];simpa using (by linarith : 0<v+B)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (by linarith))
        (mul_pos h (by linarith))
  unfold harmonicBarrierRadius
  field_simp
  ring

theorem harmonicBarrierRadius_displacement_bounds {B t r v : ℝ}
    (hB : 0<B) (ht : t∈Icc (0:ℝ) 1) (hv : 0 ≤ v) (hvr : v ≤ r) :
    t*(r-v) ≤ r-harmonicBarrierRadius B t r v ∧
      r-harmonicBarrierRadius B t r v ≤ t*((r+B)/(v+B))*(r-v) := by
  have hr : 0 ≤ r := hv.trans hvr
  have hR : 0<r+B := by linarith
  have hV : 0<v+B := by linarith
  let d := (1-t)*(v+B)+t*(r+B)
  have hdlo : v+B ≤ d := by dsimp [d];nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hvr)]
  have hdhi : d ≤ r+B := by dsimp [d];nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hvr)]
  have hd : 0<d := hV.trans_le hdlo
  have hnum : 0 ≤ t*(r-v) := mul_nonneg ht.1 (sub_nonneg.mpr hvr)
  rw [harmonicBarrierRadius_displacement hB ht hr hv]
  change t*(r-v) ≤ t*(r+B)*(r-v)/d ∧
    t*(r+B)*(r-v)/d ≤ t*((r+B)/(v+B))*(r-v)
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdhi hnum]
  · have hn : 0 ≤ t*(r+B)*(r-v) :=
      mul_nonneg (mul_nonneg ht.1 hR.le) (sub_nonneg.mpr hvr)
    have hh := div_le_div_of_nonneg_left hn hV hdlo
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

theorem harmonic_downward_fraction_bound {B t r v z C : ℝ}
    (hB : 0<B) (ht : t∈Icc (0:ℝ) 1) (hv : 0 ≤ v) (hvr : v ≤ r)
    (hzv : z ≤ v) (hzr : z<r) (hC : (r+B)/(v+B) ≤ C) :
    0 ≤ (r-harmonicBarrierRadius B t r v)/(r-z) ∧
      (r-harmonicBarrierRadius B t r v)/(r-z) ≤ C*t := by
  have hs := harmonicBarrierRadius_displacement_bounds hB ht hv hvr
  have hd : 0<r-z := sub_pos.mpr hzr
  have hdisp : 0 ≤ r-harmonicBarrierRadius B t r v :=
    (mul_nonneg ht.1 (sub_nonneg.mpr hvr)).trans hs.1
  constructor
  · exact div_nonneg hdisp hd.le
  · apply (div_le_iff₀ hd).mpr
    have hmul := mul_le_mul_of_nonneg_right hC (mul_nonneg ht.1 (sub_nonneg.mpr hvr))
    have hCpos : 0 ≤ C := (div_nonneg (by linarith : 0 ≤ r+B) (by linarith : 0 ≤ v+B)).trans hC
    have hmore := mul_le_mul_of_nonneg_left (by linarith : r-v ≤ r-z) (mul_nonneg hCpos ht.1)
    nlinarith

theorem harmonic_downward_gain {B t r v z e : ℝ}
    (hB : 0<B) (ht : t∈Icc (0:ℝ) 1) (hv : 0 ≤ v) (hvr : v ≤ r)
    (hzv : z ≤ v) (hzr : z<r) (he : 0 ≤ e) :
    e*t*(r-v)*(r-z) ≤
      e*((r-harmonicBarrierRadius B t r v)/(r-z))*(z-r)^2 := by
  have hd : r-z≠0 := (sub_pos.mpr hzr).ne'
  have hs := (harmonicBarrierRadius_displacement_bounds hB ht hv hvr).1
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg he (by linarith : 0 ≤ r-z))
  have hid : e*((r-harmonicBarrierRadius B t r v)/(r-z))*(z-r)^2=
      e*(r-harmonicBarrierRadius B t r v)*(r-z) := by
    field_simp
    ring
  rw [hid]
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
