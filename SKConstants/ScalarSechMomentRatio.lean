module

public import SKConstants.ScalarProcessGenerator
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

def scalarSech (x : ℝ) : ℝ := 1/Real.cosh x

theorem scalarSech_pos (x : ℝ) : 0 < scalarSech x := one_div_pos.mpr (Real.cosh_pos x)
theorem scalarSech_le_one (x : ℝ) : scalarSech x ≤ 1 := by
  simpa only [scalarSech,div_one] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (Real.one_le_cosh x)
theorem continuous_scalarSech : Continuous scalarSech :=
  continuous_const.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')
theorem scalarSech_abs (x : ℝ) : scalarSech |x|=scalarSech x := by
  simp only [scalarSech,Real.cosh_abs]

theorem scalarSech_antitoneOn : AntitoneOn scalarSech (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  exact one_div_le_one_div_of_le (Real.cosh_pos x)
    (Real.cosh_strictMonoOn.monotoneOn hx hy hxy)

theorem scalarDefect_eq_scalarSech_sq (x : ℝ) : scalarDefect x=(scalarSech x)^2 := by
  rw [scalarDefect_eq_inv_cosh_sq]
  simp only [scalarSech,div_pow,one_pow]

theorem hasDerivAt_scalarSech (x : ℝ) :
    HasDerivAt scalarSech (-Real.tanh x*scalarSech x) x := by
  have h := (Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne'
  unfold scalarSech
  simp only [one_div]
  convert h using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem integrable_scalarSech_pow (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun x : ℝ => (scalarSech x)^n) := by
  apply integrable_inv_cosh.mono' (continuous_scalarSech.pow n).measurable.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    simp only [Pi.pow_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (scalarSech_pos x).le n)]
    change (scalarSech x)^n ≤ scalarSech x
    simpa only [pow_one] using pow_le_pow_of_le_one (scalarSech_pos x).le (scalarSech_le_one x) hn)

theorem hasDerivAt_scalarSechMomentPrimitive (x : ℝ) :
    HasDerivAt (fun x => Real.tanh x*(scalarSech x)^3)
      (4*(scalarSech x)^5-3*(scalarSech x)^3) x := by
  have h := (hasDerivAt_tanh_scalar x).mul ((hasDerivAt_scalarSech x).pow 3)
  convert h using 1
  rw [scalarDefect_eq_scalarSech_sq]
  have ht : (Real.tanh x)^2=1-(scalarSech x)^2 := by
    rw [← scalarDefect_eq_scalarSech_sq]
    dsimp [scalarDefect]
    ring
  simp only [Pi.pow_apply,Nat.cast_ofNat,Nat.add_one_sub_one]
  linear_combination 3*(scalarSech x)^3*ht

theorem integral_scalarSechMomentDifference_zero :
    (∫ x : ℝ, 4*(scalarSech x)^5-3*(scalarSech x)^3)=0 := by
  apply integral_eq_zero_of_hasDerivAt_of_integrable hasDerivAt_scalarSechMomentPrimitive
  · exact ((integrable_scalarSech_pow 5 (by omega)).const_mul 4).sub
      ((integrable_scalarSech_pow 3 (by omega)).const_mul 3)
  · have hct : Continuous Real.tanh := continuous_iff_continuousAt.mpr
      (fun x => (hasDerivAt_tanh_scalar x).continuousAt)
    apply (integrable_scalarSech_pow 3 (by omega)).mono'
      (hct.mul (continuous_scalarSech.pow 3)).measurable.aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      simp only [Pi.mul_apply,Pi.pow_apply,norm_mul]
      rw [Real.norm_eq_abs (scalarSech x ^ 3),abs_of_nonneg (pow_nonneg (scalarSech_pos x).le 3)]
      have ht : ‖Real.tanh x‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using (Real.abs_tanh_lt_one x).le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht
        (pow_nonneg (scalarSech_pos x).le 3))

theorem scalarEvenDecreasingWeight_bound (w : ℝ → ℝ) (heven : ∀ x,w (-x)=w x)
    (hmono : AntitoneOn w (Ici (0 : ℝ))) (x : ℝ) : w x ≤ w 0 := by
  have he : w |x|=w x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx),heven]
  rw [← he]
  exact hmono (by simp) (abs_nonneg x) (abs_nonneg x)

theorem integrable_scalarEvenDecreasingWeight_sech_pow
    (w : ℝ → ℝ) (hwm : Measurable w) (hwpos : ∀ x,0 ≤ w x)
    (heven : ∀ x,w (-x)=w x) (hmono : AntitoneOn w (Ici (0 : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) : Integrable (fun x => w x*(scalarSech x)^n) := by
  apply ((integrable_scalarSech_pow n hn).const_mul (w 0)).mono'
    (hwm.mul (continuous_scalarSech.pow n).measurable).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    simp only [Pi.mul_apply,Pi.pow_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hwpos x) (pow_nonneg (scalarSech_pos x).le n))]
    exact mul_le_mul_of_nonneg_right (scalarEvenDecreasingWeight_bound w heven hmono x)
      (pow_nonneg (scalarSech_pos x).le n))

theorem scalarEvenDecreasingWeight_sech_fifth_ge_three_quarters_third
    (w : ℝ → ℝ) (hwm : Measurable w) (hwpos : ∀ x,0 ≤ w x)
    (heven : ∀ x,w (-x)=w x) (hmono : AntitoneOn w (Ici (0 : ℝ))) :
    (3/4 : ℝ)*(∫ x : ℝ,w x*(scalarSech x)^3) ≤
      ∫ x : ℝ,w x*(scalarSech x)^5 := by
  let a := Real.artanh (1/2 : ℝ)
  have ha : 0 ≤ a := (Real.artanh_pos (by norm_num : (1/2 : ℝ) ∈ Ioo 0 1)).le
  have hroot : (scalarSech a)^2=3/4 := by
    rw [← scalarDefect_eq_scalarSech_sq]
    dsimp [scalarDefect,a]
    rw [Real.tanh_artanh (by norm_num : (1/2 : ℝ) ∈ Ioo (-1) 1)]
    norm_num
  have he (x : ℝ) : w |x|=w x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (lt_of_not_ge hx),heven]
  have hp (x : ℝ) : w a*(4*(scalarSech x)^5-3*(scalarSech x)^3) ≤
      w x*(4*(scalarSech x)^5-3*(scalarSech x)^3) := by
    by_cases hx : |x| ≤ a
    · have hw : w a ≤ w x := by simpa only [he] using hmono (abs_nonneg x) ha hx
      have hs : (scalarSech a)^2 ≤ (scalarSech x)^2 := by
        simpa only [scalarSech_abs] using pow_le_pow_left₀ (scalarSech_pos a).le
          (scalarSech_antitoneOn (abs_nonneg x) ha hx) 2
      have hψ : 0 ≤ 4*(scalarSech x)^5-3*(scalarSech x)^3 := by
        have hprod := mul_nonneg (show 0 ≤ 4*(scalarSech x)^2-3 by linarith [hroot])
          (pow_nonneg (scalarSech_pos x).le 3)
        nlinarith
      exact mul_le_mul_of_nonneg_right hw hψ
    · have hw : w x ≤ w a := by
        simpa only [he] using hmono ha (abs_nonneg x) (le_of_not_ge hx)
      have hs : (scalarSech x)^2 ≤ (scalarSech a)^2 := by
        have h := scalarSech_antitoneOn (a := a) (b := |x|) ha (abs_nonneg x) (le_of_not_ge hx)
        simpa only [scalarSech_abs] using pow_le_pow_left₀ (scalarSech_pos |x|).le h 2
      have hψ : 4*(scalarSech x)^5-3*(scalarSech x)^3 ≤ 0 := by
        have hprod := mul_nonpos_of_nonpos_of_nonneg (show 4*(scalarSech x)^2-3 ≤ 0 by linarith [hroot])
          (pow_nonneg (scalarSech_pos x).le 3)
        nlinarith
      exact mul_le_mul_of_nonpos_right hw hψ
  have hi3 := integrable_scalarEvenDecreasingWeight_sech_pow w hwm hwpos heven hmono 3 (by omega)
  have hi5 := integrable_scalarEvenDecreasingWeight_sech_pow w hwm hwpos heven hmono 5 (by omega)
  have hdiff : Integrable (fun x => w x*(4*(scalarSech x)^5-3*(scalarSech x)^3)) := by
    convert (hi5.const_mul 4).sub (hi3.const_mul 3) using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  have hbase : Integrable (fun x => 4*(scalarSech x)^5-3*(scalarSech x)^3) :=
    ((integrable_scalarSech_pow 5 (by omega)).const_mul 4).sub
    ((integrable_scalarSech_pow 3 (by omega)).const_mul 3)
  have h := integral_mono (hbase.const_mul (w a)) hdiff hp
  rw [integral_const_mul,integral_scalarSechMomentDifference_zero,mul_zero] at h
  have heq : (∫ x,w x*(4*(scalarSech x)^5-3*(scalarSech x)^3)) =
      4*(∫ x,w x*(scalarSech x)^5)-3*(∫ x,w x*(scalarSech x)^3) := by
    rw [show (fun x => w x*(4*(scalarSech x)^5-3*(scalarSech x)^3)) =
      (fun x => 4*(w x*(scalarSech x)^5)-3*(w x*(scalarSech x)^3)) from by funext x; ring,
      integral_sub (hi5.const_mul 4) (hi3.const_mul 3),integral_const_mul,integral_const_mul]
  rw [heq] at h
  linarith

end SKConstants
