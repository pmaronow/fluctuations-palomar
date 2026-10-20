module

public import ComparisonActualHighWallRadiusScalarModulus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Hierarchy
open scoped Topology

theorem comparison_positive_wall_radius_absolute_cubic_rescaling
    (f : ℝ→ℝ) {a b x : ℝ} (hab : a ≤ b) (hx : 0 < x) :
    (∫t in Icc a b,|f (x*t)/x^3|)=
      (∫r in Ioo (x*a) (x*b),|f r|)/x^4 := by
  simp_rw [abs_div,abs_of_pos (pow_pos hx 3)]
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_left (fun r=>|f r|) hx.ne',
    intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le),
    ←integral_Ioc_eq_integral_Ioo,smul_eq_mul]
  field_simp

end OAI.SKFluctuations.LaplaceWindowFormalization
