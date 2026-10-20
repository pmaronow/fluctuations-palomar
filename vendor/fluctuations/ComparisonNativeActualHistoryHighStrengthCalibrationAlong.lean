module

public import ComparisonNativeLocalTemperatureCalibration
public import ComparisonNativeActualScalarGoodPointOffFloor
public import ComparisonNativeActualHighFlatWeightedPointAlong
public import ComparisonNativeActualWeightedCapTravelAlong
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

theorem exists_actual_selected_bad_history_high_strength_scalar_calibration_along
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
    (hlarge : Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
      atTop atTop) :
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
  let Ck := 2+Cs
  have Hweighted : ∀ᶠn in atTop,∃p : (M n).Potential,
      ∀ᵐu,u∈Icc (0:ℝ) 1 → u ≤ b*(M n).xs → p.H ((M n).R u) ≤ 0 →
        |laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
          (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)| ≤ (M n).xs^3 := by
    have Hrate := (actual_weighted_cap_travel_rate_tendsto_zero_along hdelta dim hdim).eventually
      (eventually_le_nhds zero_lt_one)
    filter_upwards [actual_high_strength_flat_weighted_point_along hdelta hcl hAz
      dim hdim M hlarge b hbpos.le,eventually_actual_cap_log_loss_le_along dim hdim M,Hrate]
      with n hn hnLog hnRate
    obtain ⟨p,hp⟩ := hn
    refine ⟨p,?_⟩
    filter_upwards [hp] with u hu hui hub hnonpos
    have H := (hu hui hub hnonpos).trans (hnLog.trans hnRate)
    simpa only [one_mul] using (div_le_iff₀ (pow_pos (M n).hxs 3)).mp H
  have Hfloor := hdim.eventually (eventually_actual_minimum_floor_mass_small
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=1)
    hC0 (by linarith only [hm,hdelta] : 0 < 3*m+delta) zero_lt_one)
  have hCk : 0 ≤ Ck := by dsimp only [Ck];positivity
  have Hsmall : ∀ᶠn in atTop,Ck*(M n).xs^2 ≤ (T-epsilon)*c/2 := by
    have H := (hxlim.pow 2).const_mul Ck
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero] at H
    exact H.eventually (eventually_le_nhds (by positivity))
  have Hunit := hxlim.eventually (eventually_le_nhds zero_lt_one)
  have Heta := hetalim.eventually (eventually_le_nhds zero_lt_one)
  refine ⟨c/2,Cs+Ck/(T-epsilon),1+Ck/(T-epsilon),by positivity,by positivity,by positivity,?_⟩
  filter_upwards [Hband,Hgap,Hnear,Hweighted,Hfloor,Hsmall,Hunit,Heta]
    with n hnBand hnGap hnNear hnWeighted hnFloor hnSmall hnUnit hnEta
  obtain ⟨htotal,hnGap⟩ := hnGap
  obtain ⟨p,hpWeighted⟩ := hnWeighted
  have hfloor : (M n).context.N^(-delta)*(M n).context.U ≤ (M n).xs := by
    simpa only [one_mul] using hnFloor (M n) (M n).xs le_rfl
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
  have hIntegral : (∫u in 0..b*(M n).xs, |f u|) <
      (M n).xs^3*((b-a)*(M n).xs-(M n).context.N^(-delta)*(M n).context.U) := by
    have H := mul_le_mul_of_nonneg_right hnEta (pow_nonneg (M n).hxs.le 4)
    have Hpow := pow_pos (M n).hxs 4
    have HF := mul_le_mul_of_nonneg_left hfloor (pow_pos (M n).hxs 3).le
    change (∫u in 0..b*(M n).xs, |f u|) ≤ eta n*(M n).xs^4 at hnGap
    dsimp only [b]
    nlinarith only [hnGap,H,Hpow,HF]
  obtain ⟨u,hu,hnonpos,hres,huWeighted⟩ := p.exists_scalar_good_point_off_floor
    f ha.le (show a < b by dsimp only [b];linarith) hBand.1 hfi hIntegral
    (fun u=>u∈Icc (0:ℝ) 1 → u ≤ b*(M n).xs → p.H ((M n).R u) ≤ 0 →
      |laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)| ≤ (M n).xs^3)
    (hpWeighted.mono (fun u hu _=>hu))
  have hu01 : u ∈ Icc (0:ℝ) 1 :=
    ⟨((mul_pos ha (M n).hxs).trans hu.1).le,hu.2.le.trans hBand.1⟩
  obtain ⟨hSlo,hShi,_⟩ := hBand.2 u ⟨hu.1.le,hu.2.le⟩
  have hSu : 0 ≤ orderedPathS (dim n+1) (M n).bf (M n).hf u :=
    (M n).mass_mean_nonneg hu01
  have Hnear := hnNear u ⟨hu01.1,hu.2.le⟩
  have Hweighted := huWeighted hu01 hu.2.le hnonpos
  have hclock : |actualMixedClock (dim n+1) (M n).bf (M n).hf u-
      (T-epsilon)*orderedPathS (dim n+1) (M n).bf (M n).hf u| ≤ Ck*(M n).xs^3 := by
    let S := orderedPathS (dim n+1) (M n).bf (M n).hf u
    let e := laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)
    have hid : comparisonNativeScalarClock ((M n).h u) ((M n).b u) e ((M n).R u) S-
        (T-epsilon)*S = (M n).h u+((M n).b u-(T-epsilon))*S+e*((M n).R u-S) := by
      unfold comparisonNativeScalarClock
      ring
    rw [(M n).inherited_mixed_clock_eq_nativeScalarClock hu01]
    change |comparisonNativeScalarClock ((M n).h u) ((M n).b u) e ((M n).R u) S-
      (T-epsilon)*S| ≤ _
    rw [hid]
    have HE : |e*((M n).R u-S)| ≤ (M n).xs^3 := by
      rw [show e*((M n).R u-S)=-(e*(S-(M n).R u)) by ring,abs_neg]
      exact Hweighted
    have HB := mul_le_mul Hnear.1 hShi hSu
      (show (0:ℝ) ≤ 1*(M n).xs^2 by positivity)
    have H := (abs_add_le ((M n).h u+((M n).b u-(T-epsilon))*S)
      (e*((M n).R u-S))).trans
      (add_le_add (abs_add_le ((M n).h u) (((M n).b u-(T-epsilon))*S)) le_rfl)
    rw [abs_mul,abs_of_nonneg hSu] at H
    dsimp only [Ck]
    nlinarith only [H,HE,HB,Hnear.2]
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
