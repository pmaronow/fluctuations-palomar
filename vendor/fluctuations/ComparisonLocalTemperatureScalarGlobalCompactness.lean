module

public import ComparisonLocalTemperatureScalarCompactness
public import RescaledProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 3000000

theorem comparison_local_scalar_limits_of_initial_slope {T S R A σ : ℝ}
    (hT : 0<T) (hS : 0<S) (hR : 0≤R) (hA : 0≤A)
    {α : ℕ→boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {x : ℕ→ℝ}
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop,0<x n)
    (hc : ∀n q,ContinuousWithinAt (α n).val (Ici q) q)
    (hcap : ∀ᶠ n in atTop,(α n).val ((S/T)*(x n*R))≤A*x n)
    (U : ℝ→ℝ) (hUi : IntegrableOn U (Icc (0:ℝ) R))
    (hU : ∀ᵐ t ∂volume,t∈Ioc (0:ℝ) R→
      Tendsto (fun n=>(α n).val ((S/T)*(x n*t))/x n) atTop (𝓝 (U t)))
    (hσ : Tendsto (fun n=>comparisonLocalScalarSlope hT S (α n) (x n) 0) atTop (𝓝 σ)) :
    let F := fun t=>S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
      2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t
    let p := fun t=>σ+∫s in 0..t,F s
    ContinuousOn p (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S (α n) (x n)) p atTop (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonLocalScalarResponse hT S (α n) (x n))
      (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  let Fn := fun n=>comparisonLocalScalarFlux hT S (α n) (x n)
  let F := fun t=>S^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
    2*S^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t
  let p := fun t=>σ+∫s in 0..t,F s
  have hid : IntegrableOn (fun t : ℝ=>t) (Icc (0:ℝ) R) := continuous_id.integrableOn_Icc
  have hFi : IntegrableOn F (Icc (0:ℝ) R) := (hid.const_mul _).sub (hUi.const_mul _)
  have hpc : ContinuousOn p (Icc (0:ℝ) R) := by
    have hpprim : ContinuousOn (fun t=>∫s in 0..t,F s) (Icc (0:ℝ) R) := by
      simpa only [uIcc_of_le hR] using intervalIntegral.continuousOn_primitive_interval
        (show IntegrableOn F (uIcc (0:ℝ) R) by simpa only [uIcc_of_le hR] using hFi)
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
  have hp := comparison_scalar_first_primitive_uniform Fn F
    (fun n=>comparisonLocalScalarSlope hT S (α n) (x n) 0) hFni hFi hL1 hσ
  have hk : 0<S/T := div_pos hS hT
  have hr : Tendsto (fun n=>(S/T)*(x n*R)) atTop (𝓝 0) := by
    simpa using (hx.mul_const R).const_mul (S/T)
  have hsmall : ∀ᶠ n in atTop,(S/T)*(x n*R)≤1 := (hr.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h=>h.le
  have hpnative : TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S (α n) (x n))
      p atTop (Icc (0:ℝ) R) := by
    apply hp.congr
    filter_upwards [hxp,hsmall] with n hn hs t ht
    exact (comparison_local_scalar_slope_primitive hT hS (α n) hn ht.1
      ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hn.le) hk.le).trans hs) (hc n)).symm
  have hresp := comparison_scalar_second_primitive_uniform hR
    (fun n=>comparisonLocalScalarSlope hT S (α n) (x n)) p
    (Eventually.of_forall fun n=>(comparison_local_scalar_slope_continuous hT (α n)).integrableOn_Icc)
    hpc.integrableOn_Icc hpnative
  refine ⟨hpc,hpnative,?_⟩
  apply hresp.congr
  filter_upwards [hxp,hsmall] with n hn hs t ht
  exact (comparison_local_scalar_response_primitive hT hS (α n) hn ht.1
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hn.le) hk.le).trans hs) (hc n)).symm

theorem comparison_local_scalar_caps_ambient {T S : ℝ} (hT : 0<T) (hS : 0<S)
    (α : ℕ→boundedMassProfiles) (x : ℕ→ℝ) (hxp : ∀n,0<x n)
    (hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠ n in atTop,(α n).val ((S/T)*(x n*R))≤A*x n) :
    ∀R : ℝ,0<R→∃A : ℝ,∀ᶠ n in atTop,(α n).val (x n*R)/x n≤A := by
  intro R hR
  have hk : 0<S/T := div_pos hS hT
  obtain ⟨A,_,hA⟩ := hcap (R/(S/T)) (div_pos hR hk)
  refine ⟨A,?_⟩
  filter_upwards [hA] with n hn
  rw [show (S/T)*(x n*(R/(S/T)))=x n*R by field_simp] at hn
  exact (div_le_iff₀ (hxp n)).mpr hn

theorem comparison_local_joint_scalar_radius_compactness {T S R0 c B : ℝ}
    (hT : 0<T) (hS : 0<S) (hR0 : 0<R0) (hc0 : 0<c) (hB : 0≤B)
    (alpha radiusCDF : ℕ→boundedMassProfiles) (x : ℕ→ℝ)
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀n,0<x n)
    (hc : ∀n q,ContinuousWithinAt (alpha n).val (Ici q) q)
    (hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠ n in atTop,(alpha n).val ((S/T)*(x n*R))≤A*x n)
    (hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠ n in atTop,(radiusCDF n).val (x n*R)/x n≤A)
    (hcal : ∀ᶠ n in atTop,∃q,c*x n≤q ∧ q≤R0*x n ∧
      |scalarCovarianceResponse hT (alpha n) (S*q)-q|≤B*(x n)^3) :
    ∃(beta radiusLimit : boundedMassProfiles) (U V : NonnegativeMassProfile)
      (sigma : ℝ) (phi : ℕ→ℕ),
      StrictMono phi ∧ Tendsto (alpha ∘ phi) atTop (𝓝 beta) ∧
      Tendsto (radiusCDF ∘ phi) atTop (𝓝 radiusLimit) ∧
      (∀t : ℝ,Tendsto (fun n=>(alpha (phi n)).val ((S/T)*(x (phi n)*t))/x (phi n))
        atTop (𝓝 (U.mass t))) ∧
      (∀t : ℝ,Tendsto (fun n=>(radiusCDF (phi n)).val (x (phi n)*t)/x (phi n))
        atTop (𝓝 (V.mass t))) ∧
      let F := fun t=>S^3*(scalarTailSpatialJet hT beta 4 0 0)^2*t-
        2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3*U.mass t
      let p := fun t=>sigma+∫s in 0..t,F s
      ∀R : ℝ,0<R→ ContinuousOn p (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S (alpha (phi n)) (x (phi n)))
          p atTop (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarResponse hT S (alpha (phi n)) (x (phi n)))
          (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  have hk : 0<S/T := div_pos hS hT
  have hnormcap := comparison_local_scalar_caps_ambient hT hS alpha x hxp hcap
  obtain ⟨beta,radiusLimit,Uambient,V,phi,hphi,halpha,hradius,hUambient,hV⟩ :=
    profile_pair_and_rescalings_tendsto_subseq alpha radiusCDF x hxp hnormcap hradiusCap
  let U : NonnegativeMassProfile := {
    mass := fun t=>Uambient.mass ((S/T)*t)
    nonneg := fun t=>Uambient.nonneg _
    monotone := fun _ _ h=>Uambient.monotone (mul_le_mul_of_nonneg_left h hk.le) }
  have hU (t : ℝ) : Tendsto
      (fun n=>(alpha (phi n)).val ((S/T)*(x (phi n)*t))/x (phi n))
      atTop (𝓝 (U.mass t)) := by
    simpa only [mul_left_comm (x _) (S/T)] using hUambient ((S/T)*t)
  have hUi (R : ℝ) : IntegrableOn U.mass (Icc (0:ℝ) R) := by
    apply (integrable_const (U.mass R)).mono' U.monotone.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (U.nonneg t)] using U.monotone ht.2
  obtain ⟨A,hA,hAn⟩ := hcap R0 hR0
  obtain ⟨sigma,psi,hpsi,_,_,hp,_⟩ :=
    comparison_local_temperature_scalar_compactness hT hS hR0.le hA hc0 hB
      halpha (hx.comp hphi.tendsto_atTop) (Eventually.of_forall fun n=>hxp (phi n))
      (fun n q=>hc (phi n) q) (hphi.tendsto_atTop.eventually hAn) U.mass (hUi R0)
      (Eventually.of_forall fun t _=>hU t) (hphi.tendsto_atTop.eventually hcal)
  have hsigma : Tendsto
      (fun n=>comparisonLocalScalarSlope hT S (alpha (phi (psi n))) (x (phi (psi n))) 0)
      atTop (𝓝 sigma) := by
    simpa only [Function.comp_apply,intervalIntegral.integral_same,add_zero]
      using hp.tendsto_at ⟨le_rfl,hR0.le⟩
  refine ⟨beta,radiusLimit,U,V,sigma,phi ∘ psi,hphi.comp hpsi,
    halpha.comp hpsi.tendsto_atTop,hradius.comp hpsi.tendsto_atTop,
    fun t=>(hU t).comp hpsi.tendsto_atTop,fun t=>(hV t).comp hpsi.tendsto_atTop,?_⟩
  dsimp only
  intro R hR
  obtain ⟨AR,hAR,hARn⟩ := hcap R hR
  exact comparison_local_scalar_limits_of_initial_slope hT hS hR.le hAR
    (halpha.comp hpsi.tendsto_atTop) (hx.comp (hphi.comp hpsi).tendsto_atTop)
    (Eventually.of_forall fun n=>hxp (phi (psi n))) (fun n q=>hc (phi (psi n)) q)
    ((hphi.comp hpsi).tendsto_atTop.eventually hARn) U.mass (hUi R)
    (Eventually.of_forall fun t _=>(hU t).comp hpsi.tendsto_atTop) hsigma

theorem comparison_local_scalar_global_compactness {T S R0 c B : ℝ}
    (hT : 0<T) (hS : 0<S) (hR0 : 0<R0) (hc0 : 0<c) (hB : 0≤B)
    (alpha : ℕ→boundedMassProfiles) (x : ℕ→ℝ)
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀n,0<x n)
    (hc : ∀n q,ContinuousWithinAt (alpha n).val (Ici q) q)
    (hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠ n in atTop,(alpha n).val ((S/T)*(x n*R))≤A*x n)
    (hcal : ∀ᶠ n in atTop,∃q,c*x n≤q ∧ q≤R0*x n ∧
      |scalarCovarianceResponse hT (alpha n) (S*q)-q|≤B*(x n)^3) :
    ∃(beta : boundedMassProfiles) (U : NonnegativeMassProfile) (sigma : ℝ) (phi : ℕ→ℕ),
      StrictMono phi ∧ Tendsto (alpha ∘ phi) atTop (𝓝 beta) ∧
      (∀t : ℝ,Tendsto (fun n=>(alpha (phi n)).val ((S/T)*(x (phi n)*t))/x (phi n))
        atTop (𝓝 (U.mass t))) ∧
      let F := fun t=>S^3*(scalarTailSpatialJet hT beta 4 0 0)^2*t-
        2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3*U.mass t
      let p := fun t=>sigma+∫s in 0..t,F s
      ∀R : ℝ,0<R→ ContinuousOn p (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S (alpha (phi n)) (x (phi n)))
          p atTop (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarResponse hT S (alpha (phi n)) (x (phi n)))
          (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  obtain ⟨beta,_,U,_,sigma,phi,hphi,halpha,_,hU,_,hlimits⟩ :=
    comparison_local_joint_scalar_radius_compactness hT hS hR0 hc0 hB alpha alpha x hx hxp hc hcap
      (comparison_local_scalar_caps_ambient hT hS alpha x hxp hcap) hcal
  exact ⟨beta,U,sigma,phi,hphi,halpha,hU,hlimits⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
