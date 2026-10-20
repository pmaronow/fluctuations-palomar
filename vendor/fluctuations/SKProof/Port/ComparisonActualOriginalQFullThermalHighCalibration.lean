module

public import ComparisonNativeLocalTemperatureCalibration
public import SKProof.Port.ComparisonActualOriginalQFullThermalFullHighResponse
public import SKProof.Port.ComparisonActualOriginalQHighCalibratedMassBand
public import SKProof.Port.ComparisonActualOriginalQScalarGoodPointOffFloor
public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.OriginalQWeightedCapCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000
set_option linter.unusedVariables false
theorem exists_actual_comparable_context_HIGH_scalar_calibration_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2)
      atTop atTop) :
    ∃c R B : ℝ,0 < c ∧ 0 < R ∧ 0 ≤ B ∧
      ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∃q : ℝ,c*(M n).xs ≤ q ∧ q ≤ R*(M n).xs ∧
          |scalarCovarianceResponse (G.hT)
            ((M n).inheritedScalarMassProfileBare (G.hT) htotal)
            (T*q)-q| ≤ B*(M n).xs^3 := by
  have hTemp : 0 < T := G.hT
  let a := calibratedBandStart cu Az
  let b := a+4
  let c := 3*(starMassBandConstant cu Az/cu)/4
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hbpos : 0 < b := by dsimp only [b];linarith
  have hc : 0 < c := by dsimp only [c];positivity [star_mass_band_constant_pos hcu hAz]
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  have Hclock:=G.pullback_eventually_original_q
  obtain ⟨Cs,hCs,Hband⟩ := eventually_actual_HIGH_calibrated_mass_band
    hm hdelta hroom hcl hcu hAz hC0 hCt (L:=1) (by norm_num)
    dim hdim M G hlarge (fun n=>(M n).xs) (fun _=>le_rfl) hxlim (fun _=>rfl) Hclock
  have hlo : ∀ᶠn in atTop,w0 ≤ (M n).directTestWorkingScale := by
    simpa only [hcanonical] using hWlower
  have hup : ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1 := by
    simpa only [hcanonical] using hWupper
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    actual_comparable_context_original_scalar_gap_integral_of_full_thermal_original_q
      b hbpos hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G Hfull
  have Hnear:=G.positive_band_clocks_original_q a b 1 ha hbpos.le zero_lt_one
  let Ck := 2+Cs
  have Hweighted : ∀ᶠn in atTop,∃p : (M n).Potential,
      ∀ᵐu,u∈Icc (0:ℝ) 1 → u ≤ b*(M n).xs → p.H ((M n).sweepRadius u) ≤ 0 →
        |(M n).sweepCoefficient u*
          (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u)| ≤ (M n).xs^3 := by
    have Hrate :=
      (actual_theta_zero_weighted_cap_and_origin_tendsto_zero_along_original_q
        hdelta dim hdim M).eventually
      (eventually_le_nhds zero_lt_one)
    filter_upwards [actual_strength_flat_weighted_point_along_original_q hcl hAz
      dim M (G.eventually_geometric_gates_original_q.mono fun n hn=>hn.2) hlarge b hbpos.le,Hrate]
      with n hn hnRate
    obtain ⟨p,hp⟩ := hn
    refine ⟨p,?_⟩
    filter_upwards [hp] with u hu hui hub hnonpos
    have H := (hu hui hub hnonpos).trans hnRate
    simpa only [one_mul] using (div_le_iff₀ (pow_pos (M n).hxs 3)).mp H
  have Hfloor:=G.eventually_floor_and_omission_small hC0
    (by linarith only [hm,hdelta] : 0<3*m+delta) hdim
    (fun n=>(M n).xs) (fun _=>le_rfl) (epsilon:=1) zero_lt_one
  have hCk : 0 ≤ Ck := by dsimp only [Ck];positivity
  have Hsmall : ∀ᶠn in atTop,Ck*(M n).xs^2 ≤ T*c/2 := by
    have H := (hxlim.pow 2).const_mul Ck
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero] at H
    exact H.eventually (eventually_le_nhds (by positivity))
  have Hunit := hxlim.eventually (eventually_le_nhds zero_lt_one)
  have Heta := hetalim.eventually (eventually_le_nhds zero_lt_one)
  refine ⟨c/2,Cs+Ck/T,1+Ck/T,by positivity,by positivity,by positivity,?_⟩
  filter_upwards [Hband,Hgap,Hnear,Hweighted,Hfloor,Hsmall,Hunit,Heta]
    with n hnBand hnGap hnNear hnWeighted hnFloor hnSmall hnUnit hnEta
  obtain ⟨htotal,hnGap⟩ := hnGap
  obtain ⟨p,hpWeighted⟩ := hnWeighted
  have hfloor : (M n).data.s+(M n).data.N^(-delta)*(M n).data.U ≤ (M n).xs := by
    simpa only [one_mul] using hnFloor
  simp only [mul_one] at hnBand
  have hBand : b*(M n).xs ≤ 1 ∧
      ∀u∈Icc (a*(M n).xs) (b*(M n).xs),
        c*(M n).xs ≤ orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u ∧
        orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u ≤ Cs*(M n).xs ∧
        (a/cu)*(M n).xs ≤ (M n).sweepRadius u ∧ (M n).sweepRadius u ≤ (b/cl)*(M n).xs ∧
        (M n).xs ≤ (M n).sweepRadius u ∧ (M n).z ≤ (M n).sweepRadius u/2 := by
    simpa only [a,b,c,mul_one] using ⟨hnBand.2.1,hnBand.2.2.1⟩
  let f := (M n).inheritedScalarCavityResidual
    (G.hT) htotal
  have hfi : IntervalIntegrable f volume 0 (b*(M n).xs) :=
    (M n).original_scalar_gap_intervalIntegrable
      (G.hT)
      ((M n).inheritedScalarMassProfileBare (G.hT) htotal)
      ⟨(mul_pos hbpos (M n).hxs).le,hBand.1⟩
  have hIntegral : (∫u in 0..b*(M n).xs, |f u|) <
      (M n).xs^3*((b-a)*(M n).xs-((M n).data.s+(M n).data.N^(-delta)*(M n).data.U)) := by
    have H := mul_le_mul_of_nonneg_right hnEta (pow_nonneg (M n).hxs.le 4)
    have Hpow := pow_pos (M n).hxs 4
    have HF := mul_le_mul_of_nonneg_left hfloor (pow_pos (M n).hxs 3).le
    change (∫u in 0..b*(M n).xs, |f u|) ≤ eta n*(M n).xs^4 at hnGap
    dsimp only [b]
    nlinarith only [hnGap,H,Hpow,HF]
  obtain ⟨u,hu,hnonpos,hres,huWeighted⟩ := p.exists_scalar_good_point_off_floor
    f ha.le (show a < b by dsimp only [b];linarith) hBand.1 hfi hIntegral
    (fun u=>u∈Icc (0:ℝ) 1 → u ≤ b*(M n).xs → p.H ((M n).sweepRadius u) ≤ 0 →
      |(M n).sweepCoefficient u*
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u)| ≤ (M n).xs^3)
    (hpWeighted.mono (fun u hu _=>hu))
  have hu01 : u ∈ Icc (0:ℝ) 1 :=
    ⟨((mul_pos ha (M n).hxs).trans hu.1).le,hu.2.le.trans hBand.1⟩
  obtain ⟨hSlo,hShi,_⟩ := hBand.2 u ⟨hu.1.le,hu.2.le⟩
  have hSu : 0 ≤ orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u :=
    (M n).mass_mean_nonneg hu01
  have Hnear := hnNear u ⟨hu.1.le,le_min hu.2.le hu01.2⟩
  have Hweighted := huWeighted hu01 hu.2.le hnonpos
  have hclock : |actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u-
      T*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u| ≤ Ck*(M n).xs^3 := by
    let S := orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u
    let e := (M n).sweepCoefficient u
    have hid : comparisonNativeScalarClock ((M n).h u) ((M n).b u) e ((M n).sweepRadius u) S-
        T*S = (M n).h u+((M n).b u-T)*S+e*((M n).sweepRadius u-S) := by
      unfold comparisonNativeScalarClock
      ring
    rw [(M n).inherited_mixed_clock_eq_nativeScalarClock hu01]
    change |comparisonNativeScalarClock ((M n).h u) ((M n).b u) e ((M n).sweepRadius u) S-
      T*S| ≤ _
    rw [hid]
    have HE : |e*((M n).sweepRadius u-S)| ≤ (M n).xs^3 := by
      rw [show e*((M n).sweepRadius u-S)=-(e*(S-(M n).sweepRadius u)) by ring,abs_neg]
      exact Hweighted
    have HB := mul_le_mul Hnear.1 hShi hSu
      (show (0:ℝ) ≤ 1*(M n).xs^2 by positivity)
    have H := (abs_add_le ((M n).h u+((M n).b u-T)*S)
      (e*((M n).sweepRadius u-S))).trans
      (add_le_add (abs_add_le ((M n).h u) (((M n).b u-T)*S)) le_rfl)
    rw [abs_mul,abs_of_nonneg hSu] at H
    dsimp only [Ck]
    nlinarith only [H,HE,HB,Hnear.2]
  refine ⟨htotal,actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u/T,?_⟩
  exact scalar_calibration_at_local_temperature
    (scalarCovarianceResponse (G.hT)
      ((M n).inheritedScalarMassProfileBare (G.hT) htotal))
    hTemp (M n).hxs hnUnit hCk hSlo hShi hclock hnSmall
    (show |orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-
      scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) htotal)
        (actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u)| ≤ 1*(M n).xs^3 by
      simpa only [one_mul,f,ActualThetaZeroOverlapMinimum.inheritedScalarCavityResidual] using hres)

end OAI.SKFluctuations.LaplaceWindowFormalization
