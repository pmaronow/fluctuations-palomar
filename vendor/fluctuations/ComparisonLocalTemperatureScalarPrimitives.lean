module

public import ComparisonScalarPrimitives

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 2600000

def comparisonLocalScalarResponse {T : ℝ} (hT : 0<T)
    (S : ℝ) (α : boundedMassProfiles) (x t : ℝ) : ℝ :=
  (scalarPlantedEnergy hT α ((S/T)*(x*t))-x*t)/x^3

def comparisonLocalScalarSlope {T : ℝ} (hT : 0<T)
    (S : ℝ) (α : boundedMassProfiles) (x t : ℝ) : ℝ :=
  (S*scalarPlantedCurvature hT α ((S/T)*(x*t))-1)/x^2

def comparisonLocalScalarFlux {T : ℝ} (hT : 0<T)
    (S : ℝ) (α : boundedMassProfiles) (x t : ℝ) : ℝ :=
  S^2*scalarCurvatureFlux hT α ((S/T)*(x*t))/x

theorem comparison_local_scalar_response_covariance {T : ℝ} (hT : 0<T)
    (S : ℝ) (α : boundedMassProfiles) (x t : ℝ) :
    comparisonLocalScalarResponse hT S α x t =
      (scalarCovarianceResponse hT α (S*(x*t))-x*t)/x^3 := by
  unfold comparisonLocalScalarResponse scalarCovarianceResponse
  congr 3
  ring

theorem comparison_local_scalar_slope_continuous {T S x : ℝ} (hT : 0<T)
    (α : boundedMassProfiles) : Continuous (comparisonLocalScalarSlope hT S α x) := by
  exact (((scalarPlantedCurvature_continuous hT α).comp
    (continuous_const.mul (continuous_const.mul continuous_id))).const_mul S |>.sub
      continuous_const).div_const _

theorem comparison_local_scalar_slope_primitive {T S x t : ℝ} (hT : 0<T)
    (hS : 0<S) (α : boundedMassProfiles) (hx : 0<x) (ht : 0≤t)
    (hxt : (S/T)*(x*t)≤1) (hc : ∀q,ContinuousWithinAt α.val (Ici q) q) :
    comparisonLocalScalarSlope hT S α x t =
      comparisonLocalScalarSlope hT S α x 0+
        ∫s in 0..t,comparisonLocalScalarFlux hT S α x s := by
  have hk : 0<S/T := div_pos hS hT
  have hh := scalarPlantedCurvature_integral_nonnegative hT α
    (mul_nonneg hk.le (mul_nonneg hx.le ht)) hxt (fun q _=>hc q)
  have he : (fun s : ℝ => scalarCurvatureFlux hT α ((S/T)*(x*s))) =
      (fun s => scalarCurvatureFlux hT α (((S/T)*x)*s)) := by funext s; congr 1; ring
  simp only [comparisonLocalScalarSlope,comparisonLocalScalarFlux,mul_zero]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul,he,
    intervalIntegral.integral_comp_mul_left _ (mul_pos hk hx).ne',mul_zero]
  simp only [smul_eq_mul]
  rw [show S / T * x * t = S / T * (x*t) by ring]
  field_simp
  rw [show S/T*(x*t)=S*x*t/T by ring] at hh
  nlinarith [congrArg (fun z : ℝ => S*z) hh]

theorem comparison_local_scalar_response_primitive {T S x t : ℝ} (hT : 0<T)
    (hS : 0<S) (α : boundedMassProfiles) (hx : 0<x) (ht : 0≤t)
    (hxt : (S/T)*(x*t)≤1) (hc : ∀q,ContinuousWithinAt α.val (Ici q) q) :
    comparisonLocalScalarResponse hT S α x t =
      ∫s in 0..t,comparisonLocalScalarSlope hT S α x s := by
  have hk : 0<S/T := div_pos hS hT
  have hh := scalarPlantedEnergy_integral_nonnegative hT α
    (mul_nonneg hk.le (mul_nonneg hx.le ht)) hxt (fun q _=>hc q)
  rw [scalarPlantedEnergy_zero,sub_zero] at hh
  have hi : IntervalIntegrable
      (fun s : ℝ=>S*scalarPlantedCurvature hT α ((S/T)*(x*s))) volume 0 t :=
    (((scalarPlantedCurvature_continuous hT α).comp
      (continuous_const.mul (continuous_const.mul continuous_id))).const_mul S).intervalIntegrable _ _
  have he : (fun s : ℝ => scalarPlantedCurvature hT α ((S/T)*(x*s))) =
      (fun s => scalarPlantedCurvature hT α (((S/T)*x)*s)) := by funext s; congr 1; ring
  simp only [comparisonLocalScalarResponse,comparisonLocalScalarSlope]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const_mul,he,
    intervalIntegral.integral_comp_mul_left _ (mul_pos hk hx).ne',mul_zero,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul,sub_zero,mul_one]
  rw [show S / T * x * t = S / T * (x*t) by ring,hh]
  field_simp

theorem comparison_local_scalar_initial_slope_bound {T S x A R c B q : ℝ}
    (hT : 0<T) (hS : 0<S) (α : boundedMassProfiles) (hx : 0<x)
    (hA : 0≤A) (hR : 0≤R) (hc : 0<c) (_hB : 0≤B)
    (hq : c*x≤q) (hqR : q≤R*x) (hq1 : (S/T)*q≤1)
    (hTq : T*((S/T)*q)≤1) (hmass : α.val ((S/T)*q)≤A*x)
    (hcont : ∀s,ContinuousWithinAt α.val (Ici s) s)
    (hcal : |scalarCovarianceResponse hT α (S*q)-q|≤B*x^3) :
    |comparisonLocalScalarSlope hT S α x 0|≤
      (B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c := by
  have hk : 0<S/T := div_pos hS hT
  have hq0 : 0<q := (mul_pos hc hx).trans_le hq
  have ht := scalarPlantedEnergy_smallClock_taylor hT α hx.le hA
    (mul_nonneg hk.le hR) (mul_nonneg hk.le hq0.le)
    (show (S/T)*q≤((S/T)*R)*x by nlinarith [mul_le_mul_of_nonneg_left hqR hk.le])
    hq1 hTq hmass (fun s _=>hcont s)
  rw [scalarPlantedEnergy_zero,sub_zero] at ht
  have hsq : T^2*scalarSmallClockFluxConstant T A ((S/T)*R)*x*((S/T)*q)^2 =
      S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*x*q^2 := by field_simp
  have hlin : T*scalarPlantedCurvature hT α 0*((S/T)*q) =
      S*scalarPlantedCurvature hT α 0*q := by field_simp
  rw [hsq,hlin] at ht
  have hcal' : |scalarPlantedEnergy hT α ((S/T)*q)-q|≤B*x^3 := by
    simpa only [scalarCovarianceResponse,show S*q/T=(S/T)*q by ring] using hcal
  have hF : 0 ≤ scalarSmallClockFluxConstant T A ((S/T)*R) := by
    unfold scalarSmallClockFluxConstant; positivity
  have hs : |(S*scalarPlantedCurvature hT α 0-1)*q|≤
      B*x^3+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*x*q^2 := by
    have hh := abs_sub (scalarPlantedEnergy hT α ((S/T)*q)-q)
      (scalarPlantedEnergy hT α ((S/T)*q)-S*scalarPlantedCurvature hT α 0*q)
    have he : (scalarPlantedEnergy hT α ((S/T)*q)-q)-
        (scalarPlantedEnergy hT α ((S/T)*q)-S*scalarPlantedCurvature hT α 0*q) =
        (S*scalarPlantedCurvature hT α 0-1)*q := by ring
    rw [he] at hh
    exact hh.trans (add_le_add hcal' ht)
  rw [abs_mul,abs_of_pos hq0] at hs
  have hq2 : q^2≤R^2*x^2 := by nlinarith [sq_nonneg (R*x-q)]
  have hcap := mul_le_mul_of_nonneg_left hq2
    (by positivity : 0≤S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*x)
  have hbase := mul_le_mul_of_nonneg_left hq
    (abs_nonneg (S*scalarPlantedCurvature hT α 0-1))
  have hdivision : c*((B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c)=
      B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2 := mul_div_cancel₀ _ hc.ne'
  have hbound : |S*scalarPlantedCurvature hT α 0-1|≤
      ((B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c)*x^2 := by
    apply (mul_le_mul_iff_left₀ hx).mp
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      c*(|S*scalarPlantedCurvature hT α 0-1| *x)≤
          B*x^3+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*x*q^2 := by nlinarith
      _ ≤ (B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)*x^3 := by nlinarith
      _ = c*(((B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c)*x^2*x) := by
        rw [show c*(((B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c)*x^2*x)=
          (c*((B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c))*x^3 by ring,hdivision]
  simp only [comparisonLocalScalarSlope,mul_zero,abs_div,abs_pow,abs_of_pos hx]
  exact (div_le_iff₀ (sq_pos_of_pos hx)).mpr hbound

end OAI.SKFluctuations.LaplaceWindowFormalization
