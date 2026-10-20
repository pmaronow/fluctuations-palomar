module

public import ComparisonNativeActualBoundedGradientCore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 3000000

theorem comparison_shape_slope_div_bound {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) :
    laplaceComparisonSlope (A*t)/t∈Icc (0:ℝ) A := by
  have hp:=laplaceComparisonSlope_mem_Ico (A*t)
  refine ⟨div_nonneg hp.1 ht,?_⟩
  by_cases hflat : A*t ≤ 1
  · simpa only [laplaceComparisonSlope,ite_eq_left hflat,zero_div] using hA
  · have hAt : 1 < A*t := lt_of_not_ge hflat
    have htp : 0 < t := by nlinarith
    exact (div_le_iff₀ htp).mpr (hp.2.le.trans hAt.le)

theorem comparison_bounded_principal_density_bound
    (s : NonnegativeMassProfile) {L A B t : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (ht : t∈Icc (0:ℝ) B) :
    |comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
      (laplaceComparisonSlope (A*t)) t (s.mass t)| ≤
        L*(2*B+2*s.mass B+A*(s.mass B)^2) := by
  have hp:=laplaceComparisonSlope_mem_Ico (A*t)
  have hs:=s.nonneg t
  have hS:=s.nonneg B
  have hsB:=s.monotone ht.2
  have hpt:=comparison_shape_slope_div_bound hA ht.1
  have hlin : (2-laplaceComparisonSlope (A*t))*t∈Icc (0:ℝ) (2*B) := by
    constructor
    · exact mul_nonneg (by linarith [hp.2]) ht.1
    · nlinarith only [mul_nonneg hp.1 ht.1,ht.2]
  have hspin : 2*(1-laplaceComparisonSlope (A*t))*s.mass t∈Icc (0:ℝ) (2*s.mass B) := by
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) (by linarith [hp.2])) hs
    · nlinarith only [mul_nonneg hp.1 hs,hsB]
  have hquad : laplaceComparisonSlope (A*t)*(s.mass t)^2/t∈Icc (0:ℝ) (A*(s.mass B)^2) := by
    rw [mul_div_right_comm]
    exact ⟨mul_nonneg hpt.1 (sq_nonneg _),
      mul_le_mul hpt.2 (pow_le_pow_left₀ hs hsB 2) (sq_nonneg _) hA⟩
  have hbracket : |(2-laplaceComparisonSlope (A*t))*t-
      2*(1-laplaceComparisonSlope (A*t))*s.mass t-
      laplaceComparisonSlope (A*t)*(s.mass t)^2/t| ≤
        2*B+2*s.mass B+A*(s.mass B)^2 := by
    apply abs_le.mpr
    constructor <;> linarith [hlin.1,hlin.2,hspin.1,hspin.2,hquad.1,hquad.2]
  unfold comparisonScaledStationarity
  rw [abs_mul,abs_of_nonneg (mul_nonneg hL (laplaceComparisonShape_pos _).le)]
  exact (mul_le_mul_of_nonneg_left hbracket (mul_nonneg hL (laplaceComparisonShape_pos _).le)).trans
    (mul_le_mul_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (laplaceComparisonShape_le_one (A*t)) hL)
      (by have hB:=ht.1.trans ht.2;positivity))

theorem comparison_bounded_principal_density_integrable
    (s : NonnegativeMassProfile) {L A a b : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (ha : 0 ≤ a) :
    IntegrableOn (fun t=>comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
      (laplaceComparisonSlope (A*t)) t (s.mass t)) (Icc a b) := by
  have hs:=s.monotone.measurable
  have hh : Measurable (fun t:ℝ=>laplaceComparisonShape (A*t)) :=
    laplaceComparisonShape_contDiff.continuous.measurable.comp (measurable_const.mul measurable_id)
  have hp : Measurable (fun t:ℝ=>laplaceComparisonSlope (A*t)) :=
    comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
  have hm : Measurable (fun t=>comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
      (laplaceComparisonSlope (A*t)) t (s.mass t)) := by
    unfold comparisonScaledStationarity
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (L*(2*b+2*s.mass b+A*(s.mass b)^2))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact comparison_bounded_principal_density_bound s hL hA ⟨ha.trans ht.1,ht.2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
