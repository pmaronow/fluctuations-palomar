module
public import SKConstants.ScalarProcessVarianceBalance
public import Mathlib.Algebra.Order.Field.GeomSum

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

lemma scalarR_le_exp_neg_half (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    scalarR z t ≤ Real.exp (-(t:ℝ)/2) := by
  rw [scalarR_eq_gaussian_integral]
  have hi : (∫ y, gaussianPDFReal z t y / (Real.cosh y)^3) ≤ 1 := by
    rw [← integral_gaussianPDFReal_eq_one z ht]
    apply integral_mono (integrable_gaussian_div_cosh_cube z t) (integrable_gaussianPDFReal z t)
    intro y
    exact div_le_self (gaussianPDFReal_nonneg z t y) (one_le_pow₀ (Real.one_le_cosh y))
  calc
    _ ≤ (Real.exp (-(t:ℝ)/2)/Real.cosh z)*1 :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ _ := by simpa only [mul_one] using div_le_self (Real.exp_pos _).le (Real.one_le_cosh z)

lemma scalarHiddenExpectedDefectSqReal_le_exp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (s : ℝ) (hs : 0 ≤ s) :
    scalarHiddenExpectedDefectSqReal P z B s ≤ Real.exp (-s/2) := by
  rcases hs.eq_or_lt with hzero | hpos
  · rw [← hzero]
    simpa using (le_abs_self (scalarHiddenExpectedDefectSqReal P z B 0)).trans
      (by simpa only [Real.norm_eq_abs] using scalarHiddenExpectedDefectSqReal_norm_le_one P z B 0)
  · rw [scalarHiddenExpectedDefectSqReal_eq_scalarR P z B hB s hpos]
    simpa only [Real.coe_toNNReal s hs] using
      scalarR_le_exp_neg_half z s.toNNReal (by exact_mod_cast (Real.toNNReal_pos.mpr hpos).ne')

lemma exp_geometric_mesh_budget (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (k : ℕ) :
    h * ∑ j ∈ Finset.range k, Real.exp (-(j:ℝ)*h/2) ≤ 4 := by
  let q := Real.exp (-h/2)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hqmul : q*(1+h/2) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (h/2)) hq0.le
    have he : q*Real.exp (h/2) = 1 := by
      dsimp [q]
      rw [← Real.exp_add]
      rw [show -h/2+h/2=0 by ring, Real.exp_zero]
    rw [he] at hm
    linarith
  have hden : h/4 ≤ 1-q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hh1)]
  have hs : (∑ j ∈ Finset.range k, Real.exp (-(j:ℝ)*h/2)) ≤ (1-q)⁻¹ := by
    have he (j:ℕ) : Real.exp (-(j:ℝ)*h/2) = q^j := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp_rw [he]
    have hg := geom_sum_mul q k
    have hb : (∑ j ∈ Finset.range k, q^j)*(1-q) ≤ 1 := by
      nlinarith [pow_nonneg hq0.le k]
    rw [inv_eq_one_div]
    exact (le_div_iff₀ (sub_pos.mpr hq1)).mpr hb
  apply (mul_le_mul_of_nonneg_left hs hh.le).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
  linarith

end SKConstants
