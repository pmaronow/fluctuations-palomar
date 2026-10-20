module

public import SKConstants.Completion.J3B.SpatialLimit
public import SKConstants.Completion.N19.Stability

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.J3B
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport

attribute [local irreducible] actualParisiFullMagnetization actualParisiFullCurvature

def physicalValueRate (β t y : ℝ) : ℝ :=
  -(actualParisiFullCurvature β t y +
    cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
      actualParisiFullMagnetization β t y ^ 2) / 2

theorem physicalValueRate_eq_cdf (β : ℝ) (hβ : β ≠ 0) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) (β ^ 2)) (y : ℝ) :
    physicalValueRate β t y = (1 / β ^ 2) *
      scalarCDFValueRate β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) (t / β ^ 2) y := by
  unfold physicalValueRate actualParisiFullCurvature actualParisiFullMagnetization scalarCDFValueRate
  rw [cdfTimeClamp_eq (parisiPhysicalTime_mem β hβ t ht)]
  field_simp

theorem physicalValue_integral_time_equation (β : ℝ) (hβ : β ≠ 0)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < β ^ 2) (y : ℝ) :
    parisiPhysicalValue β (parisiEquilibriumMeasure β) b y -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) a y =
        ∫ t in a..b, physicalValueRate β t y := by
  have hb2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
  have hqa : 0 ≤ a / β ^ 2 := div_nonneg ha hb2.le
  have hqab : a / β ^ 2 ≤ b / β ^ 2 := div_le_div_of_nonneg_right hab hb2.le
  have hqb : b / β ^ 2 < 1 := (div_lt_one hb2).mpr hb
  have h := scalarCDFValue_integral_time_equation β
    (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1) hβ hqa hqab hqb y
  simp only [parisiPhysicalValue, parisiCDFValue_eq_upstream]
  rw [h]
  symm
  calc
    _ = ∫ t in a..b, (1 / β ^ 2) *
        scalarCDFValueRate β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) (t / β ^ 2) y := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact physicalValueRate_eq_cdf β hβ t ⟨ha.trans ht.1, ht.2.trans hb.le⟩ y
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div
        (fun r => scalarCDFValueRate β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) r y) hb2.ne']
      simp only [smul_eq_mul, one_div, inv_mul_cancel_left₀ hb2.ne']

theorem physicalValueRate_abs_le (β t y : ℝ) : |physicalValueRate β t y| ≤ 1 / 2 := by
  have hm := actualParisiFullMagnetization_curvature_bounds β t y
  have hα0 := cdf_nonneg (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2)
  have hα1 := cdf_le_one (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2)
  have hsq := sq_nonneg (actualParisiFullMagnetization β t y)
  have hinner : 0 ≤ actualParisiFullCurvature β t y +
      cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
        actualParisiFullMagnetization β t y ^ 2 := add_nonneg hm.2.1 (mul_nonneg hα0 hsq)
  have hu : actualParisiFullCurvature β t y +
      cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2) *
        actualParisiFullMagnetization β t y ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right hα1 hsq, hm.2.2]
  rw [physicalValueRate, abs_div, abs_neg, abs_of_nonneg hinner]
  norm_num
  linarith

theorem physicalValueRate_spatial_bound (β t y z : ℝ) :
    |physicalValueRate β t y - physicalValueRate β t z| ≤
      ((susceptibilityLipschitzConstant : ℝ) + 2) / 2 * |y - z| := by
  let m := actualParisiFullMagnetization β t
  let a := actualParisiFullCurvature β t
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β ^ 2)
  have hm := (N19.actualParisiFullMagnetization_lipschitz β t).dist_le_mul y z
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hm
  have ha := (actualParisiFullCurvature_lipschitz β t).dist_le_mul y z
  simp only [Real.dist_eq] at ha
  have hsum : |m y + m z| ≤ 2 := by
    have hbound := (abs_add_le _ _).trans (add_le_add
      (actualParisiFullMagnetization_curvature_bounds β t y).1
      (actualParisiFullMagnetization_curvature_bounds β t z).1)
    simpa only [one_add_one_eq_two] using hbound
  have hsq : |m y ^ 2 - m z ^ 2| ≤ 2 * |y - z| := by
    calc
      _ = |m y - m z| * |m y + m z| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |y - z| * 2 := mul_le_mul hm hsum (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  have hα : |α| ≤ 1 := by rw [abs_of_nonneg (cdf_nonneg _ _)]; exact cdf_le_one _ _
  have hmul : |α * (m y ^ 2 - m z ^ 2)| ≤ 2 * |y - z| := by
    rw [abs_mul]
    exact (mul_le_mul hα hsq (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have he : physicalValueRate β t y - physicalValueRate β t z =
      -(a y - a z + α * (m y ^ 2 - m z ^ 2)) / 2 := by unfold physicalValueRate; dsimp [a, m, α]; ring
  rw [he, abs_div, abs_neg]
  have hab := (abs_add_le (a y - a z) (α * (m y ^ 2 - m z ^ 2))).trans (add_le_add ha hmul)
  norm_num
  nlinarith

end SKConstants.Completion.J3B
