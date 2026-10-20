module

public import ComparisonNativeActualComparableBandHighCalibration
public import ComparisonNativeActualComparableBandScalarCuts
public import ComparisonNativeActualHistoryHighJointScalarFactoryAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
theorem exists_actual_selected_bad_history_high_scalar_compactness_of_total_along_comparable_macro
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
 :
    let hT := G.hT
    let alpha := fun n=>(M n).inheritedScalarMassProfile hT (htotal n)
    let radiusCDF := fun n=>(M n).actualRadiusMassProfile
    let x := fun n=>(M n).xs
    ∃(beta radiusLimit : boundedMassProfiles) (U V : NonnegativeMassProfile)
      (sigma : ℝ) (phi : ℕ→ℕ),
      StrictMono phi ∧ Tendsto (alpha ∘ phi) atTop (𝓝 beta) ∧
      Tendsto (radiusCDF ∘ phi) atTop (𝓝 radiusLimit) ∧
      (∀t : ℝ,Tendsto (fun n=>(alpha (phi n)).val ((T/T)*(x (phi n)*t))/x (phi n))
        atTop (𝓝 (U.mass t))) ∧
      (∀t : ℝ,Tendsto (fun n=>(radiusCDF (phi n)).val (x (phi n)*t)/x (phi n))
        atTop (𝓝 (V.mass t))) ∧
      let F := fun t=>T^3*(scalarTailSpatialJet hT beta 4 0 0)^2*t-
        2*T^2*(scalarTailSpatialJet hT beta 2 0 0)^3*U.mass t
      let p := fun t=>sigma+∫s in 0..t,F s
      ∀R : ℝ,0<R→ ContinuousOn p (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT T (alpha (phi n)) (x (phi n)))
          p atTop (Icc (0:ℝ) R) ∧
        TendstoUniformlyOn (fun n=>comparisonLocalScalarResponse hT T (alpha (phi n)) (x (phi n)))
          (fun t=>∫s in 0..t,p s) atTop (Icc (0:ℝ) R) := by
  have hTemp : 0 < T := G.hT
  let hT : 0<T := G.hT
  let alpha := fun n=>(M n).inheritedScalarMassProfile hT (htotal n)
  let radiusCDF := fun n=>(M n).actualRadiusMassProfile
  let x := fun n=>(M n).xs
  have hxp : ∀n,0<x n := fun n=>(M n).hxs
  have hx : Tendsto x atTop (𝓝 0) := G.xs_zero
  have Hcaps := actual_comparable_context_original_scalar_cdf_caps
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G htotal
  have hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠn in atTop,(alpha n).val ((T/T)*(x n*R))≤A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩ := Hcaps.2 R hR
    exact ⟨A,hA.le,HA.mono fun n hn=>hn (htotal n)⟩
  have hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠn in atTop,(radiusCDF n).val (x n*R)/x n≤A := by
    intro R hR
    obtain ⟨A,hA,HA,_⟩ :=
      actual_comparable_context_compact_original_scalar_cuts
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M G htotal R hR
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
  obtain ⟨c,R0,B,hc,hR0,hB,Hcal⟩ :=
    exists_actual_comparable_context_HIGH_scalar_calibration
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical w0 hw0 hWlower hWupper
      hcompare hlarge
  have hcal : ∀ᶠn in atTop,∃q,c*x n≤q ∧ q≤R0*x n ∧
      |scalarCovarianceResponse hT (alpha n) (T*q)-q|≤B*(x n)^3 := by
    filter_upwards [Hcal] with n hn
    obtain ⟨ht,q,hq⟩ := hn
    exact ⟨q,hq⟩
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩ :=
    comparison_local_joint_scalar_radius_compactness hT hTemp hR0 hc hB alpha radiusCDF x hx hxp
      (fun n q=>(M n).inheritedScalarMassProfile_right_continuous hT (htotal n) q)
      hcap hradiusCap hcal
  exact ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩

theorem actual_selected_bad_history_high_strength_support_zero_along_comparable_macro
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (V g : ℝ→ℝ) {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (hV : ∀a ≤ R,Tendsto (fun n=>(quantileMassProfile (M n).R
      (fun u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)).val
          ((M n).xs*a)/(M n).xs) atTop (𝓝 (V a)))
    (hsupport : ∀e : ℝ,0 < e→t+e < R→V (t-e) < V (t+e))
    (hG : ∀Rclock : ℝ,0<Rclock→ TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock : ℝ,0<Rclock→ ContinuousOn g (Icc (0:ℝ) Rclock)) : g t=0 := by
  have hTemp : 0 < T := G.hT
  let C:=starMassBandConstant cu Az+cu*(|R|+1)+1
  have hCbase:=star_mass_band_constant_pos hcu hAz
  have hC : 0 < C:=by dsimp only [C];positivity
  have hCband : starMassBandConstant cu Az ≤ C:=by
    dsimp only [C]
    have H : 0 ≤ cu*(|R|+1):=by positivity
    linarith
  have hRC : R < C/cu:=by
    apply (lt_div_iff₀ hcu).mpr
    dsimp only [C]
    have H:=mul_le_mul_of_nonneg_right (le_abs_self R) hcu.le
    nlinarith
  let v:=fun n=>min (C*(M n).xs) 1
  have hxspos n : 0 < (M n).xs:=(M n).hxs
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):= G.xs_zero
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (hxspos n).le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*(M n).xs:=min_le_left _ _
  have hcut : ∀ᶠn in atTop,(M n).xs*R < (M n).R (v n):=by
    have Hsmall : ∀ᶠn in atTop,C*(M n).xs ≤ 1:=by
      have H:=hxlim.const_mul C
      simpa only [mul_zero] using H.eventually (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
    filter_upwards [Hsmall] with n hn
    dsimp only [v]
    rw [min_eq_left hn]
    have HR:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (hxspos n) le_rfl hCband hn (show C*(M n).xs∈Icc (C*(M n).xs) (C*(M n).xs) from
        ⟨le_rfl,le_rfl⟩)).1
    have H:=mul_lt_mul_of_pos_right hRC (hxspos n)
    exact (show (M n).xs*R < (C/cu)*(M n).xs by nlinarith only [H]).trans_le HR
  have hlo : ∀ᶠn in atTop,w0 ≤ (M n).canonicalDirectTestBandScale := by
    simpa only [hcanonical] using hWlower
  have hup : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1 := by
    simpa only [hcanonical] using hWupper
  have Hresponse:=actual_comparable_context_full_HIGH_response
    C hC hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G
    (Eventually.of_forall hcompare) hw0 hlo hup hlarge htotal v hv hvc g hG hg
  have Hmass:=comparison_actual_radius_cdf_support_mass (fun n=>(M n).R)
    (fun n=>(M n).xs) v V
    (fun n=>(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
    (fun n u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)
    hxspos hv hcut hV htR hsupport
  exact comparison_scalar_zero_of_positive_mass_on_compact
    (fun n=>comparisonNormalizedClockMass (M n).xs (v n)) (fun _=>inferInstance)
    (fun n (z : ParisiFinite.OrderPoint)=>(M n).R z/(M n).xs)
    (fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/(T*(M n).xs))
    _ g ht htR
    (fun n=>((comparisonSweepQuantile_continuous (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).measurable.comp
        measurable_subtype_coe).div_const _)
    (fun n=>(Hresponse.1 n).abs) (fun n=>(Hresponse.2.2.1 n).abs)
    Hresponse.2.1 Hresponse.2.2.2 Hmass (hG R (ht.trans htR))
    ((hg R (ht.trans htR)).continuousAt (Icc_mem_nhds ht htR))

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_of_total_along_comparable_macro
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧ Nonempty
      (ActualInheritedLocalScalarLimitData (G.hT)
        T (fun n=>M (phi n)) (fun n=>htotal (phi n))) := by
  have hTemp : 0 < T := G.hT
  let hT : 0<T := G.hT
  let alpha := fun n=>(M n).inheritedScalarMassProfile hT (htotal n)
  let x := fun n=>(M n).xs
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩ :=
    exists_actual_selected_bad_history_high_scalar_compactness_of_total_along_comparable_macro
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical w0 hw0 hWlower hWupper
      hcompare hlarge htotal
  let p := comparisonLocalScalarLimitSlope hT T beta U sigma
  let g := comparisonLocalScalarLimitResponse hT T beta U sigma
  have Hphysical : ∀R : ℝ,0<R→ ContinuousOn p (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT T
        (alpha (phi n)) (x (phi n))) p atTop (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT (alpha (phi n))) T (x (phi n)))
        g atTop (Icc (0:ℝ) R) := by
    intro R hR
    have H := Hlimits R hR
    refine ⟨H.1,H.2.1,?_⟩
    apply H.2.2.congr
    exact Eventually.of_forall fun n t _=>comparison_local_scalar_response_eq_rescaled
      hT (alpha (phi n)) (x (phi n)) t
  have Hcontinuous : ∀R : ℝ,0<R→ ContinuousOn g (Icc (0:ℝ) R) := by
    intro R hR
    have H := Hphysical R hR
    have Hi : IntegrableOn p (uIcc (0:ℝ) R) := by
      simpa only [uIcc_of_le hR.le] using H.1.integrableOn_Icc
    change ContinuousOn (fun r=>∫s in 0..r,p s) (Icc (0:ℝ) R)
    simpa only [uIcc_of_le hR.le] using intervalIntegral.continuousOn_primitive_interval Hi
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
  exact actual_selected_bad_history_high_strength_support_zero_along_comparable_macro
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    w0 hw0 (hphi.tendsto_atTop.eventually hWlower) (hphi.tendsto_atTop.eventually hWupper) (fun n=>hcompare (phi n))
    (hlarge.comp hphi.tendsto_atTop) (fun n=>htotal (phi n))
    V.mass g ht hRt (fun a _=>hV a) (fun e he _=>hsupport e he) (fun R hR=>(Hphysical R hR).2.2) Hcontinuous

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_along_comparable_macro
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        Nonempty (ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal)  := by
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp G.total_root
  let shift:=fun n : ℕ=>n+n0
  have hshift : StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij n0
  have ht0 : ∀n,∀u∈Icc (0:ℝ) 1,(M (shift n)).h u+(M (shift n)).b u ≤ T:=
    fun n=>(Hn0 (n+n0) (Nat.le_add_left n0 n)).1
  obtain ⟨psi,hpsi,Hlimit⟩:=exists_actual_selected_bad_history_high_joint_scalar_limit_of_total_along_comparable_macro
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (shift n)) (hdim.comp hshift.tendsto_atTop) (fun n=>M (shift n))
    (G.comp shift hshift) (fun n=>W (shift n)) (fun n=>hcanonical (shift n))
    w0 hw0 (hshift.tendsto_atTop.eventually hWlower) (hshift.tendsto_atTop.eventually hWupper) (fun n=>hcompare (shift n)) (hlarge.comp hshift.tendsto_atTop) ht0
  exact ⟨shift ∘ psi,hshift.comp hpsi,fun n=>ht0 (psi n),Hlimit⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
