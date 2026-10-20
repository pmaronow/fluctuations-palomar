module

public import RescaledScalarFlux

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem scalarCurvatureFlux_rescaled_integral_tendsto {T R A : ℝ} (hT : 0<T)
    (hR : 0≤R) (hA : 0≤A)
    {α : ℕ → boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {x : ℕ → ℝ}
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop, 0<x n)
    (hc : ∀ n q, ContinuousWithinAt (α n).val (Ici q) q)
    (hcap : ∀ᶠ n in atTop, (α n).val (x n*R)≤A*x n)
    (U : ℝ → ℝ)
    (hU : ∀ᵐ t ∂volume, t ∈ Ioc (0:ℝ) R →
      Tendsto (fun n => (α n).val (x n*t)/x n) atTop (𝓝 (U t))) :
    Tendsto (fun n => ∫ t in 0..R, T^2*scalarCurvatureFlux hT (α n) (x n*t)/x n)
      atTop (𝓝 (∫ t in 0..R,
        T^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
          2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t)) := by
  have hsmall : ∀ᶠ n in atTop, x n*R≤1 ∧ T*(x n*R)≤1 := by
    have hr : Tendsto (fun n => x n*R) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const R
    have htr : Tendsto (fun n => T*(x n*R)) atTop (𝓝 0) := by simpa only [mul_zero] using hr.const_mul T
    filter_upwards [hr.eventually (gt_mem_nhds zero_lt_one), htr.eventually (gt_mem_nhds zero_lt_one)] with n hn ht
    exact ⟨hn.le, ht.le⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (F := fun n t => T^2*scalarCurvatureFlux hT (α n) (x n*t)/x n)
    (f := fun t => T^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
          2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t)
    (μ := volume) (a := (0:ℝ)) (b := R)
    (fun _ => T^2*scalarSmallClockFluxConstant T A R)
  · apply Eventually.of_forall
    intro n
    have hm : Measurable (fun t : ℝ => scalarCurvatureFlux hT (α n) (x n*t)) :=
      (scalarCurvatureFlux_measurable hT (α n)).comp (measurable_id.const_mul (x n))
    exact ((hm.const_mul (T^2)).div_const (x n)).aestronglyMeasurable
  · filter_upwards [hxp,hsmall,hcap] with n hn hs hcn
    apply Eventually.of_forall
    intro t ht
    rw [uIoc_of_le hR] at ht
    have hqt : 0≤x n*t := mul_nonneg hn.le ht.1.le
    have hqR : x n*t≤R*x n := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hn.le]
    have hq1 : x n*t≤1 := by nlinarith
    have hTq : T*(x n*t)≤1 := by nlinarith [mul_le_mul_of_nonneg_left (show x n*t≤x n*R by nlinarith) hT.le]
    have hmass : (α n).val (x n*t)≤A*x n :=
      ((α n).property.2 (by nlinarith : x n*t≤x n*R)).trans hcn
    have hb := scalarCurvatureFlux_smallClock hT (α n) hn.le hA hR hqt hqR hq1 hTq hmass
      (fun s _ => hc n s)
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (sq_nonneg T),abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg T)
    simpa only [mul_assoc] using hh
  · exact intervalIntegrable_const
  · filter_upwards [hU] with t hUt
    intro ht
    rw [uIoc_of_le hR] at ht
    exact scalarCurvatureFlux_rescaled_tendsto hT hα hx hxp ht.1 hc (hUt ht)

end OAI.SKFluctuations.LaplaceWindowFormalization
