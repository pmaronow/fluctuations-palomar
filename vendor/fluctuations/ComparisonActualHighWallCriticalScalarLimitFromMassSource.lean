module

public import ComparisonActualHighWallCriticalJointLawCompactness
public import ComparisonActualHighWallConditionalDirectProfile
public import ComparisonActualHighWallOriginsAlong
public import ComparisonLocalTemperatureScalarReadout
public import ComparisonCriticalPositiveWallSpinProfileCompactness
public import ComparisonActualHighWallCriticalMassSourceSupportZero

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 24000000

theorem exists_actual_high_wall_critical_scalar_limit_of_mass_source
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hMassSource : ∀C>0,Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse hT
            ((M n).data.scalarMassProfile (M n).alpha)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/
        (M n).xs^4) atTop (𝓝 0)) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,
          ((M (phi n)).hf u:ℝ)+((M (phi n)).bf u:ℝ)≤T,
      ∃d : ActualHighWallLocalScalarLimitData hT T
        (fun n=>M (phi n)) htotal,
        d.U.mass=ᵐ[volume] d.V.mass := by
  let htotal : ∀n,∀u∈Icc (0:ℝ) 1,
      ((M n).hf u:ℝ)+((M n).bf u:ℝ)≤T := by
    intro n u hu
    simpa only [←hTeq n] using (M n).data.total_clock_le (M n).alpha u hu
  have hscalarEq (n : ℕ) :
      (M n).inheritedScalarMassProfile hT (htotal n)=
        (M n).data.scalarMassProfile (M n).alpha := by
    cases hTeq n
    rfl
  have hGammaEq (n : ℕ) :
      scalarCovarianceResponse hT
        ((M n).data.scalarMassProfile (M n).alpha)=
      scalarCovarianceResponse (M n).data.hTpos
        ((M n).data.scalarMassProfile (M n).alpha) := by
    cases hTeq n
    rfl
  have hC : 0 < calibratedBandStart cu Az+4 := by
    have H := calibrated_band_start_pos hcu hAz
    linarith
  have hgapCal := hMassSource (calibratedBandStart cu Az+4) hC
  have hgapCalOriginal : Tendsto (fun n=>
      (∫u in 0..(calibratedBandStart cu Az+4)*(M n).xs,
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse (M n).data.hTpos
            ((M n).data.scalarMassProfile (M n).alpha)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/
        (M n).xs^4) atTop (𝓝 0) := by
    apply hgapCal.congr'
    filter_upwards [] with n
    simp only [hGammaEq n]
  obtain ⟨c,R0,B,hc,hR0,hB,hcalOriginal⟩ :=
    ActualHighWallOverlapMinimum.exists_actual_high_wall_critical_scalar_calibration_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hT dim hdim M
      hfixed hx hsRatio (fun n=>by rw [hTeq n]) hgapCalOriginal
  have hcal : ∀ᶠn in atTop,∃q,c*(M n).xs≤q ∧ q≤R0*(M n).xs ∧
      |scalarCovarianceResponse hT
        ((M n).data.scalarMassProfile (M n).alpha) (T*q)-q|≤
        B*(M n).xs^3 := by
    filter_upwards [hcalOriginal] with n hn
    obtain ⟨q,hqlo,hqhi,hqres⟩ := hn
    refine ⟨q,hqlo,hqhi,?_⟩
    simpa only [hTeq n,←hGammaEq n] using hqres
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,ha,hr,hU,hV,hUV,Hlimits⟩ :=
    actual_high_wall_critical_joint_compactness_with_equal_laws_of_calibration
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT hc hR0 hB
      dim hdim M hfixed hTeq hx hsRatio hcal
  let P : (n:ℕ)→ActualHighWallOverlapMinimum (dim (phi n)+1)
      m delta cl cu Az C0 Ct D Bclock := fun n=>M (phi n)
  let dimP : ℕ→ℕ := fun n=>dim (phi n)
  let htotalP : ∀n,∀u∈Icc (0:ℝ) 1,
      ((P n).hf u:ℝ)+((P n).bf u:ℝ)≤T :=
    fun n=>htotal (phi n)
  have hdimP : Tendsto dimP atTop atTop :=
    hdim.comp hphi.tendsto_atTop
  have hxP : Tendsto (fun n=>(P n).xs) atTop (𝓝 0) :=
    hx.comp hphi.tendsto_atTop
  have hsRatioP : Tendsto (fun n=>(P n).data.s/(P n).xs) atTop (𝓝 0) :=
    hsRatio.comp hphi.tendsto_atTop
  have hMassP : ∀C>0,Tendsto (fun n=>
      (∫u in 0..C*(P n).xs,
        |orderedPathS (dimP n+1) (P n).bf (P n).hf u-
          scalarCovarianceResponse hT ((P n).data.scalarMassProfile (P n).alpha)
            (actualMixedClock (dimP n+1) (P n).bf (P n).hf u)|)/
        (P n).xs^4) atTop (𝓝 0) := by
    intro C hC
    exact (hMassSource C hC).comp hphi.tendsto_atTop
  let g := comparisonLocalScalarLimitResponse hT T beta U sigma
  have Hphysical : ∀Q : ℝ,0<Q→
      ContinuousOn (comparisonLocalScalarLimitSlope hT T beta U sigma)
        (Icc (0:ℝ) Q) ∧
      TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT T
        ((P n).inheritedScalarMassProfile hT (htotalP n)) (P n).xs)
        (comparisonLocalScalarLimitSlope hT T beta U sigma)
        atTop (Icc (0:ℝ) Q) ∧
      TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT
          ((P n).inheritedScalarMassProfile hT (htotalP n))) T (P n).xs)
        g atTop (Icc (0:ℝ) Q) := by
    intro Q hQ
    obtain ⟨hcont,hslope,hresp⟩ := Hlimits Q hQ
    refine ⟨hcont,?_,?_⟩
    · simpa only [P,htotalP,hscalarEq] using hslope
    · have hresp' : TendstoUniformlyOn
          (fun n=>comparisonRescaledScalarResponse
            (scalarCovarianceResponse hT
              ((P n).data.scalarMassProfile (P n).alpha)) T (P n).xs)
          g atTop (Icc (0:ℝ) Q) := by
        apply hresp.congr
        exact Eventually.of_forall fun n t _=>
          comparison_local_scalar_response_eq_rescaled hT
            ((P n).data.scalarMassProfile (P n).alpha) (P n).xs t
      simpa only [P,htotalP,hscalarEq] using hresp'
  have hgc : ∀Q>0,ContinuousOn g (Icc (0:ℝ) Q) := by
    intro Q hQ
    have Hi : IntegrableOn
        (comparisonLocalScalarLimitSlope hT T beta U sigma)
        (uIcc (0:ℝ) Q) := by
      simpa only [uIcc_of_le hQ.le] using (Hphysical Q hQ).1.integrableOn_Icc
    change ContinuousOn (fun r=>∫s in 0..r,
      comparisonLocalScalarLimitSlope hT T beta U sigma s) (Icc (0:ℝ) Q)
    simpa only [uIcc_of_le hQ.le] using
      intervalIntegral.continuousOn_primitive_interval Hi
  have hsupport : ∀t : ℝ, (0<t) →
      (t ∈ comparisonIncrementSupport V.mass) → g t=0 :=
    actual_high_wall_critical_mass_source_support_zero
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT
      dimP hdimP P (fun n=>hfixed (phi n)) (fun n=>hTeq (phi n))
      hxP hsRatioP hMassP V hV g
      (fun Q hQ=>by
        simpa only [P,htotalP,hscalarEq] using (Hphysical Q hQ).2.2) hgc
  have Hcoeff := comparison_local_scalar_native_ode_coefficients hT hT beta
  let htotalOut : ∀n,∀u∈Icc (0:ℝ) 1,
      ((M (phi n)).hf u:ℝ)+((M (phi n)).bf u:ℝ)≤T :=
    htotalP
  let d : ActualHighWallLocalScalarLimitData hT T
      (fun n=>M (phi n)) htotalOut := {
    origin_small :=
      ActualHighWallOverlapMinimum.rmin_over_larger_scale_tendsto_zero
        hdelta dimP hdimP P (fun n=>(P n).xs)
        (fun n=>(hfixed (phi n)).ge)
    omitted_small := hsRatioP
    beta := beta
    radiusLimit := radiusLimit
    U := U
    V := V
    sigma := sigma
    ambient_limit := by simpa only [P,htotalOut,hscalarEq] using ha
    radius_limit := hr
    scalar_cdf_limit := by
      intro t
      simpa only [P,htotalOut,hscalarEq,div_self hT.ne',one_mul] using hU t
    radius_cdf_limit := hV
    limits := Hphysical
    positive_coefficients := ⟨Hcoeff.1,Hcoeff.2.1⟩
    coefficient_ratio := Hcoeff.2.2
    support_zero := hsupport }
  exact ⟨phi,hphi,htotalOut,d,hUV⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
