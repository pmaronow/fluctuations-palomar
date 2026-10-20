module

public import ComparisonNativeLocalTemperatureCalibration
public import ComparisonInitialIntegralGoodPoint
public import ComparisonNativeActualHistoryOriginalScalarGapIntegralAlong
public import ComparisonSignedCavityActualRegularCalibratedBand
public import ComparisonNativeActualHistoryNearBareClocks
public import ComparisonNativeActualSelectedBadHistoryReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_bounded_strength_scalar_calibration_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
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
    (Kstrength : ℝ) (hKstrength : 0 ≤ Kstrength)
    (hbounded : ∀ᶠn in atTop,
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ Kstrength*(M n).xs^2) :
    ∃c R B : ℝ,0 < c ∧ 0 < R ∧ 0 ≤ B ∧
      ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∃q : ℝ,c*(M n).xs ≤ q ∧ q ≤ R*(M n).xs ∧
          |scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
            ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) htotal)
            ((T-epsilon)*q)-q| ≤ B*(M n).xs^3 := by
  let a := calibratedBandStart cu Az
  let b := a+4
  let c := 3*(starMassBandConstant cu Az/cu)/4
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hbpos : 0 < b := by dsimp only [b];linarith
  have hc : 0 < c := by dsimp only [c];positivity [star_mass_band_constant_pos hcu hAz]
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨ps,Hps⟩ := Hhistory.literal_readout epsilon shell hb hh
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
    filter_upwards [Hps] with n hn
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha T epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
      (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl
  obtain ⟨Cs,hCs,Hband⟩ := eventually_actual_regular_calibrated_mass_band
    hm hdelta hroom hcl hcu hAz hC0 hCt (L:=1) (by norm_num)
    dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl) hxlim Hclock
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along
      b hbpos hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell
      hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have Hnear := actual_selected_bad_shell_history_near_bare_clocks
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    epsilon shell hshell hb hh Hhistory (fun n=>(M n).xs)
    (Eventually.of_forall (fun _=>le_rfl)) hxlim b 1 hbpos.le zero_lt_one
  let Cm := b/cl+Cs
  let Ck := 1+Cs+Kstrength*Cm
  have hCm : 0 ≤ Cm := by dsimp only [Cm];positivity
  have hCk : 0 ≤ Ck := by dsimp only [Ck];positivity
  have Hsmall : ∀ᶠn in atTop,Ck*(M n).xs^2 ≤ (T-epsilon)*c/2 := by
    have H := (hxlim.pow 2).const_mul Ck
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero] at H
    exact H.eventually (eventually_le_nhds (by positivity))
  have Hunit := hxlim.eventually (eventually_le_nhds zero_lt_one)
  have Heta := hetalim.eventually (eventually_le_nhds zero_lt_one)
  refine ⟨c/2,Cs+Ck/(T-epsilon),1+Ck/(T-epsilon),by positivity,by positivity,by positivity,?_⟩
  filter_upwards [Hband,Hgap,Hnear,hbounded,Hsmall,Hunit,Heta]
    with n hnBand hnGap hnNear hnBound hnSmall hnUnit hnEta
  obtain ⟨htotal,hnGap⟩ := hnGap
  simp only [mul_one] at hnBand
  have hBand : b*(M n).xs ≤ 1 ∧
      ∀u∈Icc (a*(M n).xs) (b*(M n).xs),
        c*(M n).xs ≤ orderedPathS (dim n+1) (M n).bf (M n).hf u ∧
        orderedPathS (dim n+1) (M n).bf (M n).hf u ≤ Cs*(M n).xs ∧
        (a/cu)*(M n).xs ≤ (M n).R u ∧ (M n).R u ≤ (b/cl)*(M n).xs ∧
        (M n).xs ≤ (M n).R u ∧ (M n).z ≤ (M n).R u/2 := by
    simpa only [a,b,c,mul_one] using ⟨hnBand.2.1,hnBand.2.2.1⟩
  let f := (M n).inheritedScalarCavityResidual
    (hTemp.trans_le (sub_le_self T hepsilon)) htotal
  have hfi : IntervalIntegrable f volume 0 (b*(M n).xs) :=
    (M n).original_scalar_gap_intervalIntegrable
      (hTemp.trans_le (sub_le_self T hepsilon))
      ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) htotal)
      ⟨(mul_pos hbpos (M n).hxs).le,hBand.1⟩
  have hIntegral : (∫u in 0..b*(M n).xs, |f u|) < (b-a)*(M n).xs^4 := by
    have H := mul_le_mul_of_nonneg_right hnEta (pow_nonneg (M n).hxs.le 4)
    have Hpow := pow_pos (M n).hxs 4
    change (∫u in 0..b*(M n).xs, |f u|) ≤ eta n*(M n).xs^4 at hnGap
    dsimp only [b]
    nlinarith only [hnGap,H,Hpow]
  obtain ⟨u,hu,hres⟩ := exists_abs_le_of_initial_integral_lt f (M n).hxs ha.le
    (show a < b by dsimp only [b];linarith) hfi hIntegral
  have hu01 : u ∈ Icc (0:ℝ) 1 :=
    ⟨((mul_pos ha (M n).hxs).trans hu.1).le,hu.2.le.trans hBand.1⟩
  obtain ⟨hSlo,hShi,_hRlo,hRhi,hxsR,_hz⟩ := hBand.2 u ⟨hu.1.le,hu.2.le⟩
  have hSu : 0 ≤ orderedPathS (dim n+1) (M n).bf (M n).hf u :=
    (M n).mass_mean_nonneg hu01
  have hRu : 0 ≤ (M n).R u := (M n).hxs.le.trans hxsR
  have hmismatch : |(M n).R u-orderedPathS (dim n+1) (M n).bf (M n).hf u|
      ≤ Cm*(M n).xs := by
    have H := abs_sub_le ((M n).R u) 0 (orderedPathS (dim n+1) (M n).bf (M n).hf u)
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hRu,abs_of_nonneg hSu] at H
    dsimp only [Cm]
    nlinarith only [H,hRhi,hShi]
  have hR01 := comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u
  have he : laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)
      ≤ Kstrength*(M n).xs^2 :=
    ((laplaceComparisonStrength_monotonicities_nonneg (M n).context.hd.ne' (M n).hlam.le).1
      ⟨(M n).hxs.le,hnUnit⟩ hR01 hxsR).trans hnBound
  have Hnear := hnNear u ⟨hu01.1,hu.2.le⟩
  have hclock : |actualMixedClock (dim n+1) (M n).bf (M n).hf u-
      (T-epsilon)*orderedPathS (dim n+1) (M n).bf (M n).hf u| ≤ Ck*(M n).xs^3 := by
    simpa only [one_mul,Ck] using (M n).inherited_clock_cubic_error_of_eq4
      hu01 (M n).hxs.le (show (0:ℝ) ≤ 1 by norm_num) hKstrength
      Hnear.1 Hnear.2 he hmismatch hShi
  refine ⟨htotal,actualMixedClock (dim n+1) (M n).bf (M n).hf u/(T-epsilon),?_⟩
  exact scalar_calibration_at_local_temperature
    (scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
      ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) htotal))
    hTemp (M n).hxs hnUnit hCk hSlo hShi hclock hnSmall
    (show |orderedPathS (dim n+1) (M n).bf (M n).hf u-
      scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
        ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) htotal)
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤ 1*(M n).xs^3 by
      simpa only [one_mul,f,inheritedScalarCavityResidual] using hres)

end OAI.SKFluctuations.LaplaceWindowFormalization
