module

public import ComparisonLocalTemperatureScalarPrimitives

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 2600000

theorem comparison_local_scalar_flux_bound {T S R A : ℝ} (hT : 0<T) (hS : 0<S)
    (hR : 0≤R) (hA : 0≤A) (α : ℕ→boundedMassProfiles) (x : ℕ→ℝ)
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop,0<x n)
    (hc : ∀n q,ContinuousWithinAt (α n).val (Ici q) q)
    (hcap : ∀ᶠ n in atTop,(α n).val ((S/T)*(x n*R))≤A*x n) :
    ∀ᶠ n in atTop,∀t∈Icc (0:ℝ) R,
      |comparisonLocalScalarFlux hT S (α n) (x n) t|≤
        S^2*scalarSmallClockFluxConstant T A ((S/T)*R) := by
  have hk : 0<S/T := div_pos hS hT
  have hr : Tendsto (fun n=>(S/T)*(x n*R)) atTop (𝓝 0) := by
    simpa using (hx.mul_const R).const_mul (S/T)
  have htr : Tendsto (fun n=>T*((S/T)*(x n*R))) atTop (𝓝 0) := by simpa using hr.const_mul T
  filter_upwards [hxp,hcap,hr.eventually (gt_mem_nhds zero_lt_one),
    htr.eventually (gt_mem_nhds zero_lt_one)] with n hn hcn hsmall htsmall t ht
  have hqt : 0≤(S/T)*(x n*t) := mul_nonneg hk.le (mul_nonneg hn.le ht.1)
  have hqR : (S/T)*(x n*t)≤((S/T)*R)*x n := by
    nlinarith [mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hk.le hn.le)]
  have hqR' : (S/T)*(x n*t)≤(S/T)*(x n*R) := by nlinarith
  have hq1 : (S/T)*(x n*t)≤1 := hqR'.trans hsmall.le
  have hTq : T*((S/T)*(x n*t))≤1 :=
    (mul_le_mul_of_nonneg_left hqR' hT.le).trans htsmall.le
  have hmass : (α n).val ((S/T)*(x n*t))≤A*x n :=
    ((α n).property.2 hqR').trans hcn
  have hb := scalarCurvatureFlux_smallClock hT (α n) hn.le hA
    (mul_nonneg hk.le hR) hqt hqR hq1 hTq hmass (fun s _=>hc n s)
  simp only [comparisonLocalScalarFlux,abs_div,abs_mul,abs_of_nonneg (sq_nonneg S),abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb (sq_nonneg S)

theorem comparison_local_scalar_flux_tendsto {T S t U : ℝ} (hT : 0<T) (hS : 0<S)
    {α : ℕ→boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {x : ℕ→ℝ}
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop,0<x n) (ht : 0<t)
    (hc : ∀n q,ContinuousWithinAt (α n).val (Ici q) q)
    (hU : Tendsto (fun n=>(α n).val ((S/T)*(x n*t))/x n) atTop (𝓝 U)) :
    Tendsto (fun n=>comparisonLocalScalarFlux hT S (α n) (x n) t) atTop
      (𝓝 (S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
        2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U)) := by
  have hm : Tendsto (fun n=>(α n).val (x n*((S/T)*t))/x n) atTop (𝓝 U) := by
    simpa only [mul_left_comm (x _) (S/T)] using hU
  have hf := (scalarCurvatureFlux_rescaled_tendsto hT hα hx hxp
    (mul_pos (div_pos hS hT) ht) hc hm).const_mul ((S/T)^2)
  have he : (S/T)^2*(T^3*(scalarTailSpatialJet hT β 4 0 0)^2*((S/T)*t)-
      2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U) =
      S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
        2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U := by field_simp
  rw [he] at hf
  apply hf.congr'
  exact Eventually.of_forall fun n=>by
    dsimp only [comparisonLocalScalarFlux]
    rw [show x n*((S/T)*t)=(S/T)*(x n*t) by ring]
    field_simp

theorem comparison_local_scalar_flux_L1_tendsto {T S R A : ℝ} (hT : 0<T) (hS : 0<S)
    (hR : 0≤R) (hA : 0≤A)
    {α : ℕ→boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {x : ℕ→ℝ}
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop,0<x n)
    (hc : ∀n q,ContinuousWithinAt (α n).val (Ici q) q)
    (hcap : ∀ᶠ n in atTop,(α n).val ((S/T)*(x n*R))≤A*x n)
    (U : ℝ→ℝ) (hUm : AEStronglyMeasurable U (volume.restrict (Icc (0:ℝ) R)))
    (hU : ∀ᵐ t ∂volume,t∈Ioc (0:ℝ) R→
      Tendsto (fun n=>(α n).val ((S/T)*(x n*t))/x n) atTop (𝓝 (U t))) :
    Tendsto (fun n=>∫t in Icc (0:ℝ) R,
      |comparisonLocalScalarFlux hT S (α n) (x n) t-
        (S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
          2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t)|) atTop (𝓝 0) := by
  let μ := volume.restrict (Icc (0:ℝ) R)
  let F := fun n=>comparisonLocalScalarFlux hT S (α n) (x n)
  let f := fun t=>S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
    2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t
  let C := S^2*scalarSmallClockFluxConstant T A ((S/T)*R)
  have hb := comparison_local_scalar_flux_bound hT hS hR hA α x hx hxp hc hcap
  have hFm : ∀n,AEStronglyMeasurable (F n) μ := by
    intro n
    exact ((((scalarCurvatureFlux_measurable hT (α n)).comp
      ((measurable_id.const_mul (x n)).const_mul (S/T))).const_mul (S^2)).div_const (x n)).aestronglyMeasurable
  have hfm : AEStronglyMeasurable f μ :=
    (aestronglyMeasurable_id.const_mul _).sub (hUm.const_mul _)
  have hlim : ∀ᵐ t ∂μ,Tendsto (fun n=>F n t) atTop (𝓝 (f t)) := by
    have hu : ∀ᵐ t ∂μ,t∈Ioc (0:ℝ) R→
        Tendsto (fun n=>(α n).val ((S/T)*(x n*t))/x n) atTop (𝓝 (U t)) :=
      hU.filter_mono (ae_mono Measure.restrict_le_self)
    have hn : ∀ᵐ t ∂μ,t≠(0:ℝ) := by
      have hz : ∀ᵐ t : ℝ ∂volume,t≠0 := by
        apply ae_iff.mpr
        simp only [not_not,Set.ofPred_eq_eq_singleton,measure_singleton]
      exact hz.filter_mono (ae_mono Measure.restrict_le_self)
    filter_upwards [hu,hn,ae_restrict_mem measurableSet_Icc] with t ht htn hti
    exact comparison_local_scalar_flux_tendsto hT hS hα hx hxp
      (lt_of_le_of_ne hti.1 (Ne.symm htn)) hc (ht ⟨lt_of_le_of_ne hti.1 (Ne.symm htn),hti.2⟩)
  have hfb : ∀ᵐ t ∂μ,|f t|≤C := by
    filter_upwards [hlim,ae_restrict_mem measurableSet_Icc] with t ht hti
    exact le_of_tendsto ht.abs (hb.mono fun n hn=>hn t hti)
  have hdom : ∀ᶠ n in atTop,∀ᵐ t ∂μ,‖|F n t-f t|‖≤2*C := by
    filter_upwards [hb] with n hn
    filter_upwards [hfb,ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans (by linarith [hn t hti])
  have hi := tendsto_integral_filter_of_dominated_convergence (μ:=μ)
    (bound:=fun _=>2*C)
    (Eventually.of_forall fun n=>continuous_abs.comp_aestronglyMeasurable ((hFm n).sub hfm))
    hdom (integrable_const _) (hlim.mono fun t ht=>by simpa using (ht.sub_const (f t)).abs)
  simpa only [F,f,μ,Pi.sub_apply,integral_zero] using hi

end OAI.SKFluctuations.LaplaceWindowFormalization
