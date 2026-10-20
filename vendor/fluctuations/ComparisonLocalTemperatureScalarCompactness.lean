module

public import ComparisonScalarPrimitiveLimits
public import ComparisonLocalTemperatureScalarFlux
public import Mathlib.Topology.Sequences

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 2600000

theorem comparison_local_temperature_scalar_compactness {T S R A c B : ℝ}
    (hT : 0<T) (hS : 0<S) (hR : 0≤R) (hA : 0≤A) (hc0 : 0<c) (hB : 0≤B)
    {α : ℕ→boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {x : ℕ→ℝ}
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop,0<x n)
    (hc : ∀n q,ContinuousWithinAt (α n).val (Ici q) q)
    (hcap : ∀ᶠ n in atTop,(α n).val ((S/T)*(x n*R))≤A*x n)
    (U : ℝ→ℝ) (hUi : IntegrableOn U (Icc (0:ℝ) R))
    (hU : ∀ᵐ t ∂volume,t∈Ioc (0:ℝ) R→
      Tendsto (fun n=>(α n).val ((S/T)*(x n*t))/x n) atTop (𝓝 (U t)))
    (hcal : ∀ᶠ n in atTop,∃q,c*x n≤q ∧ q≤R*x n ∧
      |scalarCovarianceResponse hT (α n) (S*q)-q|≤B*(x n)^3) :
    ∃σ : ℝ,∃φ : ℕ→ℕ,StrictMono φ ∧
      |σ|≤(B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c ∧
      let F := fun t=>S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
        2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t
      let p := fun t=>σ+∫s in 0..t,F s
      ContinuousOn p (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S (α (φ n)) (x (φ n)))
        p atTop (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonLocalScalarResponse hT S (α (φ n)) (x (φ n)))
        (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  let C := (B+S^2*scalarSmallClockFluxConstant T A ((S/T)*R)*R^2)/c
  let σn := fun n=>comparisonLocalScalarSlope hT S (α n) (x n) 0
  let Fn := fun n=>comparisonLocalScalarFlux hT S (α n) (x n)
  let F := fun t=>S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
    2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t
  have hk : 0<S/T := div_pos hS hT
  have hr : Tendsto (fun n=>(S/T)*(x n*R)) atTop (𝓝 0) := by
    simpa using (hx.mul_const R).const_mul (S/T)
  have htr : Tendsto (fun n=>T*((S/T)*(x n*R))) atTop (𝓝 0) := by simpa using hr.const_mul T
  have hsmall : ∀ᶠ n in atTop,(S/T)*(x n*R)≤1 ∧ T*((S/T)*(x n*R))≤1 := by
    filter_upwards [hr.eventually (gt_mem_nhds zero_lt_one),htr.eventually (gt_mem_nhds zero_lt_one)] with n hn ht
    exact ⟨hn.le,ht.le⟩
  have hslope : ∀ᶠ n in atTop,σn n∈Icc (-C) C := by
    filter_upwards [hxp,hsmall,hcap,hcal] with n hn hs hcn hcaln
    obtain ⟨q,hq,hqR,hqcal⟩ := hcaln
    have hqR' : (S/T)*q≤(S/T)*(x n*R) := by
      nlinarith [mul_le_mul_of_nonneg_left hqR hk.le]
    have hq1 : (S/T)*q≤1 := hqR'.trans hs.1
    have hTq : T*((S/T)*q)≤1 :=
      (mul_le_mul_of_nonneg_left hqR' hT.le).trans hs.2
    have hmass : (α n).val ((S/T)*q)≤A*x n :=
      ((α n).property.2 hqR').trans hcn
    exact abs_le.mp (comparison_local_scalar_initial_slope_bound hT hS (α n) hn hA hR hc0 hB
      hq hqR hq1 hTq hmass (hc n) hqcal)
  obtain ⟨σ,hσC,φ,hφ,hσ⟩ := isCompact_Icc.tendsto_subseq' hslope.frequently
  let p := fun t=>σ+∫s in 0..t,F s
  have hid : IntegrableOn (fun t : ℝ=>t) (Icc (0:ℝ) R) := continuous_id.integrableOn_Icc
  have hFi : IntegrableOn F (Icc (0:ℝ) R) :=
    (hid.const_mul _).sub (hUi.const_mul _)
  have hpc : ContinuousOn p (Icc (0:ℝ) R) := by
    have h : IntegrableOn F (uIcc (0:ℝ) R) := by simpa only [uIcc_of_le hR] using hFi
    have hpprim : ContinuousOn (fun t=>∫s in 0..t,F s) (Icc (0:ℝ) R) := by
      simpa only [uIcc_of_le hR] using intervalIntegral.continuousOn_primitive_interval h
    intro t ht
    exact continuousWithinAt_const.add (hpprim t ht)
  have hFnm : ∀n,AEStronglyMeasurable (Fn n) (volume.restrict (Icc (0:ℝ) R)) := by
    intro n
    exact ((((scalarCurvatureFlux_measurable hT (α n)).comp
      ((measurable_id.const_mul (x n)).const_mul (S/T))).const_mul (S^2)).div_const (x n)).aestronglyMeasurable
  have hFnb := comparison_local_scalar_flux_bound hT hS hR hA α x hx hxp hc hcap
  have hFni : ∀ᶠ n in atTop,IntegrableOn (Fn n) (Icc (0:ℝ) R) := by
    filter_upwards [hFnb] with n hn
    apply (integrable_const (S^2*scalarSmallClockFluxConstant T A ((S/T)*R))).mono' (hFnm n)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs] using hn t ht
  have hL1 := comparison_local_scalar_flux_L1_tendsto hT hS hR hA hα hx hxp hc hcap U
    hUi.aestronglyMeasurable hU
  have hφtop := hφ.tendsto_atTop
  have hp := comparison_scalar_first_primitive_uniform (fun n=>Fn (φ n)) F (σn∘φ)
    (hφtop.eventually hFni) hFi (hL1.comp hφtop) hσ
  have hpnative : TendstoUniformlyOn
      (fun n=>comparisonLocalScalarSlope hT S (α (φ n)) (x (φ n))) p atTop (Icc (0:ℝ) R) := by
    apply hp.congr
    filter_upwards [hφtop.eventually hxp,hφtop.eventually hsmall] with n hn hs t ht
    exact (comparison_local_scalar_slope_primitive hT hS (α (φ n)) hn ht.1
      ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hn.le) hk.le).trans hs.1) (hc (φ n))).symm
  have hresp := comparison_scalar_second_primitive_uniform hR
    (fun n=>comparisonLocalScalarSlope hT S (α (φ n)) (x (φ n))) p
    (Eventually.of_forall fun n=>(comparison_local_scalar_slope_continuous hT (α (φ n))).integrableOn_Icc)
    hpc.integrableOn_Icc hpnative
  refine ⟨σ,φ,hφ,abs_le.mpr hσC,hpc,hpnative,?_⟩
  apply hresp.congr
  filter_upwards [hφtop.eventually hxp,hφtop.eventually hsmall] with n hn hs t ht
  exact (comparison_local_scalar_response_primitive hT hS (α (φ n)) hn ht.1
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hn.le) hk.le).trans hs.1) (hc (φ n))).symm

end OAI.SKFluctuations.LaplaceWindowFormalization
