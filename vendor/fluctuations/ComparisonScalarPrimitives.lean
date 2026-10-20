module

public import RescaledScalarFluxIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 2000000

def comparisonActualScalarResponse {T : ℝ} (hT : 0<T)
    (α : boundedMassProfiles) (x t : ℝ) : ℝ :=
  (scalarPlantedEnergy hT α (x*t)-x*t)/x^3

def comparisonActualScalarSlope {T : ℝ} (hT : 0<T)
    (α : boundedMassProfiles) (x t : ℝ) : ℝ :=
  (T*scalarPlantedCurvature hT α (x*t)-1)/x^2

def comparisonActualScalarFlux {T : ℝ} (hT : 0<T)
    (α : boundedMassProfiles) (x t : ℝ) : ℝ :=
  T^2*scalarCurvatureFlux hT α (x*t)/x

theorem comparison_actual_scalar_slope_continuous {T x : ℝ} (hT : 0<T)
    (α : boundedMassProfiles) : Continuous (comparisonActualScalarSlope hT α x) := by
  exact (((scalarPlantedCurvature_continuous hT α).comp
    (continuous_const.mul continuous_id)).const_mul T |>.sub continuous_const).div_const _

theorem comparison_actual_scalar_slope_primitive {T x t : ℝ} (hT : 0<T)
    (α : boundedMassProfiles) (hx : 0<x) (ht : 0≤t) (hxt : x*t≤1)
    (hc : ∀q,ContinuousWithinAt α.val (Ici q) q) :
    comparisonActualScalarSlope hT α x t =
      comparisonActualScalarSlope hT α x 0+
        ∫s in 0..t,comparisonActualScalarFlux hT α x s := by
  have hh := scalarPlantedCurvature_integral_nonnegative hT α
    (mul_nonneg hx.le ht) hxt (fun q _=>hc q)
  simp only [comparisonActualScalarSlope,comparisonActualScalarFlux,mul_zero]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ hx.ne',mul_zero]
  simp only [smul_eq_mul]
  field_simp
  nlinarith [hh]

theorem comparison_actual_scalar_response_primitive {T x t : ℝ} (hT : 0<T)
    (α : boundedMassProfiles) (hx : 0<x) (ht : 0≤t) (hxt : x*t≤1)
    (hc : ∀q,ContinuousWithinAt α.val (Ici q) q) :
    comparisonActualScalarResponse hT α x t =
      ∫s in 0..t,comparisonActualScalarSlope hT α x s := by
  have hh := scalarPlantedEnergy_integral_nonnegative hT α
    (mul_nonneg hx.le ht) hxt (fun q _=>hc q)
  rw [scalarPlantedEnergy_zero,sub_zero] at hh
  have hi : IntervalIntegrable (fun s : ℝ=>T*scalarPlantedCurvature hT α (x*s)) volume 0 t :=
    (((scalarPlantedCurvature_continuous hT α).comp
      (continuous_const.mul continuous_id)).const_mul T).intervalIntegrable _ _
  simp only [comparisonActualScalarResponse,comparisonActualScalarSlope]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_mul_left _ hx.ne',
    mul_zero,intervalIntegral.integral_const]
  simp only [smul_eq_mul,sub_zero,mul_one]
  rw [hh]
  field_simp

theorem comparison_actual_scalar_initial_slope_bound {T x A R c B q : ℝ}
    (hT : 0<T) (α : boundedMassProfiles) (hx : 0<x) (hA : 0≤A) (hR : 0≤R)
    (hc : 0<c) (hB : 0≤B) (hq : c*x≤q) (hqR : q≤R*x)
    (hq1 : q≤1) (hTq : T*q≤1) (hmass : α.val q≤A*x)
    (hcont : ∀s,ContinuousWithinAt α.val (Ici s) s)
    (hcal : |scalarPlantedEnergy hT α q-q|≤B*x^3) :
    |comparisonActualScalarSlope hT α x 0|≤
      (B+T^2*scalarSmallClockFluxConstant T A R*R^2)/c := by
  have hh := scalarPlantedEnergy_calibrated_slope hT α hx hA hR hc hB hq hqR
    hq1 hTq hmass (fun s _=>hcont s) hcal
  simp only [comparisonActualScalarSlope,mul_zero,abs_div,abs_pow,abs_of_pos hx]
  exact (div_le_iff₀ (sq_pos_of_pos hx)).mpr hh

end OAI.SKFluctuations.LaplaceWindowFormalization
