module

public import ComparisonNativeActualLocalScalarLimitData
public import ComparisonNativeActualHistoryBoundedStrengthCalibrationAlong
public import ComparisonNativeActualHistoryLocalTemperatureScalarCutsAlong
public import ComparisonNativeActualHistoryBoundedSupportAlong
public import ComparisonNativeActualSelectedBadHistoryReindex

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_joint_scalar_limit_of_total_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧ Nonempty
      (ActualInheritedLocalScalarLimitData (hTemp.trans_le (sub_le_self T hepsilon))
        (T-epsilon) (fun n=>M (phi n)) (fun n=>htotal (phi n))) := by
  let hT : 0<T := hTemp.trans_le (sub_le_self T hepsilon)
  let alpha := fun n=>(M n).inheritedScalarMassProfile hT (htotal n)
  let radiusCDF := fun n=>(M n).actualRadiusMassProfile
  let x := fun n=>(M n).xs
  have hxp : ∀n,0<x n := fun n=>(M n).hxs
  have hx : Tendsto x atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hcaps := actual_selected_bad_history_local_temperature_original_scalar_cdf_caps_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M x (fun _=>le_rfl) hx epsilon shell hepsilon hshell hTemp hb hh Hhistory
  have hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠn in atTop,(alpha n).val (((T-epsilon)/T)*(x n*R))≤A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩ := Hcaps.2 R hR
    exact ⟨A,hA.le,HA.mono fun n hn=>hn (htotal n)⟩
  have hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠn in atTop,(radiusCDF n).val (x n*R)/x n≤A := by
    intro R hR
    obtain ⟨A,hA,HA,_⟩ :=
      actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim root M x (fun _=>le_rfl) hx epsilon shell hepsilon hshell hTemp hb hh Hhistory R hR
    refine ⟨A,?_⟩
    filter_upwards [HA] with n hn
    have hv : min (A*x n) 1∈Icc (0:ℝ) 1 :=
      ⟨le_min (mul_nonneg hA.le (hxp n).le) zero_le_one,min_le_right _ _⟩
    have H := quantileMassProfile_le_of_larger_clock (M n).R
      ((comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
      (fun u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u) hv hn.2
    exact (div_le_iff₀ (hxp n)).mpr (H.trans (min_le_left _ _))
  have hbounded : ∀ᶠn in atTop,
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs≤K*(M n).xs^2 := by
    filter_upwards [hwork] with n hn
    exact (div_le_iff₀ (pow_pos (M n).hxs 2)).mp hn
  obtain ⟨c,R0,B,hc,hR0,hB,Hcal⟩ :=
    exists_actual_selected_bad_history_bounded_strength_scalar_calibration_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
      hcompare K hK hbounded
  have hcal : ∀ᶠn in atTop,∃q,c*x n≤q ∧ q≤R0*x n ∧
      |scalarCovarianceResponse hT (alpha n) ((T-epsilon)*q)-q|≤B*(x n)^3 := by
    filter_upwards [Hcal] with n hn
    obtain ⟨ht,q,hq⟩ := hn
    exact ⟨q,hq⟩
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩ :=
    comparison_local_joint_scalar_radius_compactness hT hTemp hR0 hc hB alpha radiusCDF x hx hxp
      (fun n q=>(M n).inheritedScalarMassProfile_right_continuous hT (htotal n) q)
      hcap hradiusCap hcal
  let p := comparisonLocalScalarLimitSlope hT (T-epsilon) beta U sigma
  let g := comparisonLocalScalarLimitResponse hT (T-epsilon) beta U sigma
  have Hphysical : ∀R : ℝ,0<R→ ContinuousOn p (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT (T-epsilon)
        (alpha (phi n)) (x (phi n))) p atTop (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT (alpha (phi n))) (T-epsilon) (x (phi n)))
        g atTop (Icc (0:ℝ) R) := by
    intro R hR
    have H := Hlimits R hR
    refine ⟨H.1,H.2.1,?_⟩
    apply H.2.2.congr
    exact Eventually.of_forall fun n t _=>comparison_local_scalar_response_eq_rescaled
      hT (alpha (phi n)) (x (phi n)) t
  have Hcoeff := comparison_local_scalar_native_ode_coefficients hT hTemp beta
  refine ⟨phi,hphi,⟨{
    beta := beta
    radiusLimit := radiusLimit
    U := U
    V := V
    sigma := sigma
    ambient_limit := halpha
    radius_limit := hradius
    scalar_cdf_limit := hU
    radius_cdf_limit := hV
    limits := Hphysical
    positive_coefficients := ⟨Hcoeff.1,Hcoeff.2.1⟩
    coefficient_ratio := Hcoeff.2.2
    support_zero := ?_ }⟩⟩
  intro t ht hsupport
  have hRt : t<t+1 := by linarith
  have hR : 0<t+1 := by linarith
  have H := Hphysical (t+1) hR
  have hg : ContinuousAt g t := by
    have Hi : IntegrableOn p (uIcc (0:ℝ) (t+1)) := by
      simpa only [uIcc_of_le hR.le] using H.1.integrableOn_Icc
    have Hc : ContinuousOn g (Icc (0:ℝ) (t+1)) := by
      change ContinuousOn (fun r=>∫s in 0..r,p s) (Icc (0:ℝ) (t+1))
      simpa only [uIcc_of_le hR.le] using intervalIntegral.continuousOn_primitive_interval Hi
    exact Hc.continuousAt (Icc_mem_nhds ht hRt)
  exact actual_selected_bad_history_bounded_strength_support_zero_along K hK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>root (phi n)) (fun n=>M (phi n)) epsilon shell hepsilon hshell hTemp
    (hphi.tendsto_atTop.eventually hb) (hphi.tendsto_atTop.eventually hh)
    (Hhistory.comp phi hphi.tendsto_atTop) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n))
    (hphi.tendsto_atTop.eventually hwork) (fun n=>htotal (phi n))
    V.mass g ht hRt (fun a _=>hV a) (fun e he _=>hsupport e he) H.2.2 hg

end OAI.SKFluctuations.LaplaceWindowFormalization
