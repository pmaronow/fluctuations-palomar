module

public import ComparisonNativeActualHighFlatFullWeightedAlong
public import ComparisonNativeActualInitialCompactClockAlong
public import ComparisonNativeActualRegularInitialMassMismatchAlong
public import ComparisonNativeActualSequentialBareErrorAlong
public import ComparisonNativeActualHistoryNormalizedScalarGapAlong
public import ComparisonNativeActualSelectedBadHistoryInitialMismatchAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_high_strength_response_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C : ℝ) (hC : 0 < C)
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
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*(M n).xs)
    (g : ℝ→ℝ)
    (hG : ∀Rclock > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
        ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n)))
      (T-epsilon) (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let hT:=hTemp.trans_le (sub_le_self T hepsilon)
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let G:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n)))
        (T-epsilon) (M n).xs
    let q:=fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/((T-epsilon)*(M n).xs)
    (∀n,Integrable (fun z=>G n (q n z)) (nu n)) ∧
      Tendsto (fun n=>∫z,|G n (q n z)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun z=>q n z-(M n).R z/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫z,|q n z-(M n).R z/(M n).xs|∂nu n) atTop (𝓝 0) := by
  obtain ⟨_eta,_heta,_hetalim,_Henvelope,Hcavity⟩:=
    exists_actual_selected_bad_history_normalized_scalar_gap_along
      C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell
      hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have Hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity
    dim root M epsilon shell hb hh Hhistory
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    epsilon shell hshell hb hh Hhistory (fun n=>(M n).xs)
    (Eventually.of_forall fun _=>le_rfl) Hxs
  have Hbare : ∀eps > 0,∀ᶠn in atTop,∀z : ParisiFinite.OrderPoint,z.val ≤ v n →
      |(M n).b z-(T-epsilon)| ≤ eps*(M n).xs^2 ∧
        |(M n).h z| ≤ eps*(M n).xs^3 := by
    intro eps heps
    filter_upwards [Hnear C eps hC.le heps] with n hn
    intro z hz
    exact hn z ⟨z.property.1,hz.trans (hvc n)⟩
  have Hcav:=Hcavity htotal v hv (Eventually.of_forall hvc)
  have HbareRate:=actual_inherited_restricted_bare_error_of_vanishing_clocks_along
    (T:=T-epsilon) hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
    (fun _=>le_rfl) (fun n=>{z : ParisiFinite.OrderPoint | (z:ℝ) ≤ v n})
    (fun _=>measurableSet_le measurable_subtype_coe measurable_const) C hC
    (fun n z hz=>hz.trans (hvc n)) Hbare
  have Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs), |(M n).h u| ≤ (M n).xs^3 := by
    filter_upwards [Hnear C 1 hC.le (by norm_num)] with n hn u hu
    simpa only [one_mul] using (hn u hu).2
  obtain ⟨Rclock,hRclock,Hrange⟩:=actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M Hxs
    (hTemp.trans_le (sub_le_self T hepsilon)) hTemp htotal C hC Hfield
  have HrangeV : ∀ᶠn in atTop,∀z : ParisiFinite.OrderPoint,(z:ℝ) ≤ v n →
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/((T-epsilon)*(M n).xs)∈Icc (0:ℝ) Rclock := by
    filter_upwards [Hrange] with n hn z hz
    exact hn z (hz.trans (hvc n))
  have Hweighted:=actual_high_strength_full_weighted_mass_tendsto_zero_along
    hdelta hcl hAz hC0 (by linarith only [hm,hdelta]) dim hdim M hlarge C hC.le v hv hvc
    (hTemp.trans_le (sub_le_self T hepsilon)) hTemp htotal Hcav.2 HbareRate.2
    Rclock HrangeV g (hG Rclock hRclock) (hg Rclock hRclock)
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {z | (z:ℝ) ≤ v n}
  let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let S:=fun n (z : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf z
  let rad:=fun n (z : ParisiFinite.OrderPoint)=>(M n).R z
  let e:=fun n z=>laplaceComparisonStrength (M n).context.d (M n).lam (rad n z)
  let Gamma:=fun n=>scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
    ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n))
  let h0:=fun n (z : ParisiFinite.OrderPoint)=>(M n).h z
  let b0:=fun n (z : ParisiFinite.OrderPoint)=>(M n).b z
  have Hmixed n (z : ParisiFinite.OrderPoint) : comparisonScalarMassClockOn h0 b0 e S rad n z=
      actualMixedClock (dim n+1) (M n).bf (M n).hf z :=
    ((M n).inherited_mixed_clock_eq_nativeScalarClock z.property).symm
  have Hcav' n : Integrable (fun z=>(S n z-Gamma n (comparisonScalarMassClockOn h0 b0 e S rad n z))/(M n).xs^3) (nu n) := by
    simp_rw [Hmixed];exact Hcav.1 n
  have Hcav0' : Tendsto (fun n=>∫z,|(S n z-Gamma n (comparisonScalarMassClockOn h0 b0 e S rad n z))/(M n).xs^3|∂nu n) atTop (𝓝 0) := by
    simp_rw [Hmixed];exact Hcav.2
  have Hresponse:=comparison_scalar_mass_response_L1_tendsto_on nu Gamma h0 b0 e S rad
    (fun n=>(M n).xs) hTemp (fun n=>(M n).hxs.ne') Hweighted.1 Hcav' HbareRate.1
    Hweighted.2 Hcav0' HbareRate.2
  have Hsquare:=regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs) v
    (fun _=>le_rfl) Hxs Hclock C hC hv hvc
  have Hspin0:=comparison_original_mass_normalized_L1_tendsto mu (fun _=>inferInstance)
    (fun n z=>S n z-rad n z) (fun n=>(M n).xs) (fun n=>(M n).hxs) hC.le
    (fun n=>((M n).original_retained_mismatch_integrable (v n)).1)
    (fun n=>((M n).original_retained_mismatch_integrable (v n)).2)
    (fun n=>by rw [comparison_original_retained_mass_exact (hv n)];exact hvc n) Hsquare
  have Hspin n : Integrable (fun z=>S n z/(M n).xs-rad n z/(M n).xs) (nu n) := by
    simpa only [sub_div,nu,mu,comparisonNormalizedClockMass,S,rad] using
      ((((M n).original_retained_mismatch_integrable (v n)).1).smul_measure ENNReal.ofReal_ne_top).div_const (M n).xs
  have Hspin0' : Tendsto (fun n=>∫z,|S n z/(M n).xs-rad n z/(M n).xs|∂nu n) atTop (𝓝 0) := by
    simpa only [sub_div,nu,mu,comparisonNormalizedClockMass,S,rad] using Hspin0
  have HclockRate:=comparison_scalar_mass_clock_L1_tendsto_on nu h0 b0 e S rad (fun n=>(M n).xs)
    hTemp (fun n=>(M n).hxs.ne') Hxs Hspin Hweighted.1 HbareRate.1
    Hspin0' Hweighted.2 HbareRate.2
  simp_rw [Hmixed] at Hresponse HclockRate
  exact ⟨Hresponse.1,Hresponse.2,HclockRate.1,HclockRate.2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
