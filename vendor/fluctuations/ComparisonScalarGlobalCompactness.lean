module

public import ComparisonActualScalarCompactness
public import RescaledProfileHelly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 3000000

theorem comparison_scalar_limits_of_initial_slope {T R A σ : ℝ}
    (hT : 0<T) (hR : 0≤R) (hA : 0≤A)
    {α : ℕ→boundedMassProfiles} {β : boundedMassProfiles}
    (hα : Tendsto α atTop (𝓝 β)) {x : ℕ→ℝ}
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ᶠ n in atTop,0<x n)
    (hc : ∀n q,ContinuousWithinAt (α n).val (Ici q) q)
    (hcap : ∀ᶠ n in atTop,(α n).val (x n*R)≤A*x n)
    (U : ℝ→ℝ) (hUi : IntegrableOn U (Icc (0:ℝ) R))
    (hU : ∀ᵐ t ∂volume,t∈Ioc (0:ℝ) R→
      Tendsto (fun n=>(α n).val (x n*t)/x n) atTop (𝓝 (U t)))
    (hσ : Tendsto (fun n=>comparisonActualScalarSlope hT (α n) (x n) 0) atTop (𝓝 σ)) :
    let F := fun t=>T^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
      2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t
    let p := fun t=>σ+∫s in 0..t,F s
    ContinuousOn p (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonActualScalarSlope hT (α n) (x n)) p atTop (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonActualScalarResponse hT (α n) (x n))
      (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  let Fn := fun n=>comparisonActualScalarFlux hT (α n) (x n)
  let F := fun t=>T^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
    2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U t
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
      (measurable_id.const_mul (x n))).const_mul (T^2)).div_const (x n)).aestronglyMeasurable
  have hFnb := comparison_actual_scalar_flux_bound hT hR hA α x hx hxp hc hcap
  have hFni : ∀ᶠ n in atTop,IntegrableOn (Fn n) (Icc (0:ℝ) R) := by
    filter_upwards [hFnb] with n hn
    apply (integrable_const (T^2*scalarSmallClockFluxConstant T A R)).mono' (hFnm n)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs] using hn t ht
  have hL1 := comparison_actual_scalar_flux_L1_tendsto hT hR hA hα hx hxp hc hcap U
    hUi.aestronglyMeasurable hU
  have hp := comparison_scalar_first_primitive_uniform Fn F
    (fun n=>comparisonActualScalarSlope hT (α n) (x n) 0) hFni hFi hL1 hσ
  have hr : Tendsto (fun n=>x n*R) atTop (𝓝 0) := by simpa using hx.mul_const R
  have hsmall : ∀ᶠ n in atTop,x n*R≤1 := (hr.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h=>h.le
  have hpnative : TendstoUniformlyOn (fun n=>comparisonActualScalarSlope hT (α n) (x n))
      p atTop (Icc (0:ℝ) R) := by
    apply hp.congr
    filter_upwards [hxp,hsmall] with n hn hs t ht
    exact (comparison_actual_scalar_slope_primitive hT (α n) hn ht.1
      ((mul_le_mul_of_nonneg_left ht.2 hn.le).trans hs) (hc n)).symm
  have hresp := comparison_scalar_second_primitive_uniform hR
    (fun n=>comparisonActualScalarSlope hT (α n) (x n)) p
    (Eventually.of_forall fun n=>(comparison_actual_scalar_slope_continuous hT (α n)).integrableOn_Icc)
    hpc.integrableOn_Icc hpnative
  refine ⟨hpc,hpnative,?_⟩
  apply hresp.congr
  filter_upwards [hxp,hsmall] with n hn hs t ht
  exact (comparison_actual_scalar_response_primitive hT (α n) hn ht.1
    ((mul_le_mul_of_nonneg_left ht.2 hn.le).trans hs) (hc n)).symm

theorem comparison_scalar_global_compactness {T R0 c B : ℝ}
    (hT : 0<T) (hR0 : 0<R0) (hc0 : 0<c) (hB : 0≤B)
    (α : ℕ→boundedMassProfiles) (x : ℕ→ℝ)
    (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀n,0<x n)
    (hc : ∀n q,ContinuousWithinAt (α n).val (Ici q) q)
    (hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧ ∀ᶠ n in atTop,(α n).val (x n*R)≤A*x n)
    (hcal : ∀ᶠ n in atTop,∃q,c*x n≤q ∧ q≤R0*x n ∧
      |scalarPlantedEnergy hT (α n) q-q|≤B*(x n)^3) :
    ∃(β : boundedMassProfiles) (U : NonnegativeMassProfile) (σ : ℝ) (φ : ℕ→ℕ),
      StrictMono φ ∧ Tendsto (α∘φ) atTop (𝓝 β) ∧
      (∀t : ℝ,Tendsto (fun n=>(α (φ n)).val (x (φ n)*t)/x (φ n)) atTop (𝓝 (U.mass t))) ∧
      let F := fun t=>T^3*(scalarTailSpatialJet hT β 4 0 0)^2*t-
        2*T^2*(scalarTailSpatialJet hT β 2 0 0)^3*U.mass t
      let p := fun t=>σ+∫s in 0..t,F s
      ∀R : ℝ,0<R→ ContinuousOn p (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonActualScalarSlope hT (α (φ n)) (x (φ n)))
          p atTop (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonActualScalarResponse hT (α (φ n)) (x (φ n)))
          (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  have hnormcap : ∀R : ℝ,0<R→∃A : ℝ,∀ᶠ n in atTop,(α n).val (x n*R)/x n≤A := by
    intro R hR
    obtain ⟨A,_,hAn⟩ := hcap R hR
    exact ⟨A,hAn.mono fun n hn=>(div_le_iff₀ (hxp n)).mpr hn⟩
  obtain ⟨β,U,φ,hφ,hα,hU⟩ := profiles_and_rescalings_tendsto_subseq α x hxp hnormcap
  have hUi (R : ℝ) : IntegrableOn U.mass (Icc (0:ℝ) R) := by
    apply (integrable_const (U.mass R)).mono' U.monotone.measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs,abs_of_nonneg (U.nonneg t)] using U.monotone ht.2
  obtain ⟨A,hA,hAn⟩ := hcap R0 hR0
  have hxφ := hx.comp hφ.tendsto_atTop
  have hxpφ : ∀ᶠ n in atTop,0<(x∘φ) n := Eventually.of_forall fun n=>hxp (φ n)
  have hUφ : ∀ᵐ t ∂volume,t∈Ioc (0:ℝ) R0→
      Tendsto (fun n=>(α (φ n)).val (x (φ n)*t)/x (φ n)) atTop (𝓝 (U.mass t)) :=
    Eventually.of_forall fun t _=>hU t
  obtain ⟨σ,ψ,hψ,_,hpc,hp,hg⟩ := comparison_actual_scalar_compactness hT hR0.le hA hc0 hB
    hα hxφ hxpφ (fun n q=>hc (φ n) q) (hφ.tendsto_atTop.eventually hAn) U.mass
    (hUi R0) hUφ (hφ.tendsto_atTop.eventually hcal)
  have hσ : Tendsto (fun n=>comparisonActualScalarSlope hT (α (φ (ψ n))) (x (φ (ψ n))) 0)
      atTop (𝓝 σ) := by
    simpa only [Function.comp_apply,intervalIntegral.integral_same,add_zero] using hp.tendsto_at ⟨le_rfl,hR0.le⟩
  refine ⟨β,U,σ,φ∘ψ,hφ.comp hψ,hα.comp hψ.tendsto_atTop,
    fun t=>(hU t).comp hψ.tendsto_atTop,?_⟩
  dsimp only
  intro R hR
  obtain ⟨AR,hAR,hARn⟩ := hcap R hR
  exact comparison_scalar_limits_of_initial_slope hT hR.le hAR
    (hα.comp hψ.tendsto_atTop) (hx.comp (hφ.comp hψ).tendsto_atTop)
    (Eventually.of_forall fun n=>hxp (φ (ψ n))) (fun n q=>hc (φ (ψ n)) q)
    ((hφ.comp hψ).tendsto_atTop.eventually hARn) U.mass (hUi R)
    (Eventually.of_forall fun t _=>(hU t).comp hψ.tendsto_atTop) hσ

end OAI.SKFluctuations.LaplaceWindowFormalization
