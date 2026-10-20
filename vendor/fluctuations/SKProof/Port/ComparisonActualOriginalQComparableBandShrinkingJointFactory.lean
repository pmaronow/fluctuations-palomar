module

public import ComparisonNativeActualComparableBandShrinkingJointFactory
public import SKProof.Port.ComparisonActualOriginalQComparableBandShrinkingResponse
public import SKProof.Port.ComparisonActualOriginalQComparableBandScalarCuts
public import SKProof.Port.ComparisonActualOriginalQHighScalarCuts
public import SKProof.Port.ComparisonActualOriginalQScalarLimitData
public import SKProof.Port.ComparisonActualOriginalQFullThermalHighCalibration
public import SKProof.Port.ComparisonActualOriginalQLimitRigidity
public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.OriginalQWeightedCapCalibration

@[expose] public section
set_option autoImplicit false

noncomputable section
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000

theorem exists_actual_selected_bad_history_normalized_scalar_gap_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      (∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀v∈Icc (0:ℝ) 1,v ≤ Atarget*(M n).xs →
          Integrable (fun z : ParisiFinite.OrderPoint =>
            (M n).inheritedScalarCavityResidual (G.hT)
              htotal z/(M n).xs^3) (comparisonNormalizedClockMass (M n).xs v) ∧
          (∫z : ParisiFinite.OrderPoint,
            |(M n).inheritedScalarCavityResidual (G.hT)
              htotal z/(M n).xs^3| ∂comparisonNormalizedClockMass (M n).xs v) ≤ eta n) ∧
      (∀htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀v : ℕ→ℝ,(∀n,v n∈Icc (0:ℝ) 1) →
        (∀ᶠn in atTop,v n ≤ Atarget*(M n).xs) →
          (∀n,Integrable (fun z : ParisiFinite.OrderPoint =>
            (M n).inheritedScalarCavityResidual (G.hT)
              (htotal n) z/(M n).xs^3) (comparisonNormalizedClockMass (M n).xs (v n))) ∧
          Tendsto (fun n=>∫z : ParisiFinite.OrderPoint,
            |(M n).inheritedScalarCavityResidual (G.hT)
              (htotal n) z/(M n).xs^3| ∂comparisonNormalizedClockMass (M n).xs (v n))
            atTop (𝓝 0)) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_original_q
      Atarget hAtarget hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨eta,heta,hetalim,
    actual_original_scalar_gap_normalized_envelope_along_original_q
      (G.hT) hAtarget eta M hxlim Hgap,?_⟩
  intro htotal v hv hvA
  exact actual_original_scalar_gap_normalized_l1_tendsto_zero_along_original_q
    (G.hT) hAtarget eta hetalim M htotal hxlim Hgap v hv hvA

theorem exists_actual_selected_bad_history_bounded_strength_scalar_calibration_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (Kstrength : ℝ) (hKstrength : 0 ≤ Kstrength)
    (hbounded : ∀ᶠn in atTop,
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs ≤ Kstrength*(M n).xs^2) :
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
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hclock:=G.pullback_eventually_original_q
  obtain ⟨Cs,hCs,Hband⟩ := eventually_actual_regular_calibrated_mass_band
    hm hdelta hroom hcl hcu hAz hC0 hCt (L:=1) (by norm_num)
    dim hdim M G (fun n=>(M n).xs) (fun _=>le_rfl) hxlim Hclock
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_original_q
      b hbpos hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have Hnear:=G.positive_band_clocks_original_q a b 1 ha hbpos.le zero_lt_one
  let Cm := b/cl+Cs
  let Ck := 1+Cs+Kstrength*Cm
  have hCm : 0 ≤ Cm := by dsimp only [Cm];positivity
  have hCk : 0 ≤ Ck := by dsimp only [Ck];positivity
  have Hsmall : ∀ᶠn in atTop,Ck*(M n).xs^2 ≤ T*c/2 := by
    have H := (hxlim.pow 2).const_mul Ck
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero] at H
    exact H.eventually (eventually_le_nhds (by positivity))
  have Hunit := hxlim.eventually (eventually_le_nhds zero_lt_one)
  have Heta := hetalim.eventually (eventually_le_nhds zero_lt_one)
  refine ⟨c/2,Cs+Ck/T,1+Ck/T,by positivity,by positivity,by positivity,?_⟩
  filter_upwards [Hband,Hgap,Hnear,hbounded,Hsmall,Hunit,Heta]
    with n hnBand hnGap hnNear hnBound hnSmall hnUnit hnEta
  obtain ⟨htotal,hnGap⟩ := hnGap
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
  have hSu : 0 ≤ orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u :=
    (M n).mass_mean_nonneg hu01
  have hRu : 0 ≤ (M n).sweepRadius u := (M n).hxs.le.trans hxsR
  have hmismatch : |(M n).sweepRadius u-orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u|
      ≤ Cm*(M n).xs := by
    have H := abs_sub_le ((M n).sweepRadius u) 0 (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hRu,abs_of_nonneg hSu] at H
    dsimp only [Cm]
    nlinarith only [H,hRhi,hShi]
  have hR01 := (M n).sweepRadius_bounds0 u

  have he : laplaceComparisonStrength (M n).data.d (M n).lam ((M n).sweepRadius u)
      ≤ Kstrength*(M n).xs^2 :=
    ((laplaceComparisonStrength_monotonicities_nonneg (M n).data.hd.ne' (M n).hlam.le).1
      ⟨(M n).hxs.le,hnUnit⟩ hR01 hxsR).trans hnBound
  have Hnear := hnNear u ⟨hu.1.le,le_min hu.2.le hu01.2⟩
  have hclock : |actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u-
      T*orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u| ≤ Ck*(M n).xs^3 := by
    simpa only [one_mul,Ck] using (M n).inherited_clock_cubic_error_of_eq4_original_q
      hu01 (M n).hxs.le (show (0:ℝ) ≤ 1 by norm_num) hKstrength
      Hnear.1 Hnear.2 he hmismatch hShi
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

theorem actual_selected_bad_history_bounded_strength_response_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C K : ℝ) (hC : 0 < C) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*(M n).xs)
    (g : ℝ→ℝ)
    (hG : ∀Rclock > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let hT:=G.hT
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let G:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfileBare hT (htotal n)))
        T (M n).xs
    let q:=fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf z/(T*(M n).xs)
    (∀n,Integrable (fun z=>G n (q n z)) (nu n)) ∧
      Tendsto (fun n=>∫z,|G n (q n z)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun z=>q n z-(M n).sweepRadius z/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫z,|q n z-(M n).sweepRadius z/(M n).xs|∂nu n) atTop (𝓝 0) := by
  exact actual_comparable_context_shrinking_full_bounded_response_original_q C hC hm hdelta hroom hcl hcu hAz hC0 hCt
    hCcal hc0 hc01 hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
    K hK hwork htotal v hv hvc g hG hg

theorem actual_selected_bad_history_bounded_strength_support_zero_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (V g : ℝ→ℝ) {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (hV : ∀a ≤ R,Tendsto (fun n=>(quantileMassProfile (M n).sweepRadius
      (fun u _=>(M n).sweepRadius_bounds0 u)).val

          ((M n).xs*a)/(M n).xs) atTop (𝓝 (V a)))
    (hsupport : ∀e : ℝ,0 < e→t+e < R→V (t-e) < V (t+e))
    (hG : ∀Rclock : ℝ,0<Rclock→ TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
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
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (hxspos n).le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*(M n).xs:=min_le_left _ _
  have hcut : ∀ᶠn in atTop,(M n).xs*R < (M n).sweepRadius (v n):=by
    have Hsmall : ∀ᶠn in atTop,C*(M n).xs ≤ 1:=by
      have H:=hxlim.const_mul C
      simpa only [mul_zero] using H.eventually (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
    filter_upwards [Hsmall,G.positive_bands_high_original_q C hC] with n hn hnhigh
    dsimp only [v]
    rw [min_eq_left hn]
    have HR:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (hxspos n) le_rfl hCband hn hnhigh (show C*(M n).xs∈Icc (C*(M n).xs) (C*(M n).xs) from
        ⟨le_rfl,le_rfl⟩)).1
    have H:=mul_lt_mul_of_pos_right hRC (hxspos n)
    exact (show (M n).xs*R < (C/cu)*(M n).xs by nlinarith only [H]).trans_le HR
  have Hresponse:=actual_selected_bad_history_bounded_strength_response_along_comparable_shrinking_original_q
    C K hC hK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare hwork htotal v hv hvc g hG hg
  have Hmass:=comparison_actual_radius_cdf_support_mass (fun n=>(M n).sweepRadius)
    (fun n=>(M n).xs) v V
    (fun n=>((M n).sweepRadius_monotone).monotoneOn _)

    (fun n u _=>(M n).sweepRadius_bounds0 u)

    hxspos hv hcut hV htR hsupport
  exact comparison_scalar_zero_of_positive_mass_on_compact
    (fun n=>comparisonNormalizedClockMass (M n).xs (v n)) (fun _=>inferInstance)
    (fun n (z : ParisiFinite.OrderPoint)=>(M n).sweepRadius z/(M n).xs)
    (fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf z/(T*(M n).xs))
    _ g ht htR
    (fun n=>(((M n).sweepRadius_continuous).measurable.comp

        measurable_subtype_coe).div_const _)
    (fun n=>(Hresponse.1 n).abs) (fun n=>(Hresponse.2.2.1 n).abs)
    Hresponse.2.1 Hresponse.2.2.2 Hmass (hG R (ht.trans htR))
    ((hg R (ht.trans htR)).continuousAt (Icc_mem_nhds ht htR))

theorem exists_actual_selected_bad_history_bounded_joint_scalar_limit_of_total_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧ Nonempty
      (ActualOriginalQLocalScalarLimitData (G.hT)
        T (fun n=>M (phi n)) (fun n=>htotal (phi n))) := by
  have hTemp : 0 < T := G.hT
  let hT : 0<T := G.hT
  let alpha := fun n=>(M n).inheritedScalarMassProfileBare hT (htotal n)
  let radiusCDF := fun n=>(M n).actualRadiusMassProfile
  let x := fun n=>(M n).xs
  have hxp : ∀n,0<x n := fun n=>(M n).hxs
  have hx : Tendsto x atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hcaps := actual_comparable_context_original_scalar_cdf_caps_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G htotal
  have hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤ A ∧
      ∀ᶠn in atTop,(alpha n).val ((T/T)*(x n*R))≤ A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩ := Hcaps.2 R hR
    exact ⟨A,hA.le,HA.mono fun n hn=>hn (htotal n)⟩
  have hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠn in atTop,(radiusCDF n).val (x n*R)/x n≤ A := by
    intro R hR
    obtain ⟨A,hA,HA,_⟩ :=
      actual_comparable_context_compact_original_scalar_cuts_original_q
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M G htotal R hR
    refine ⟨A,?_⟩
    filter_upwards [HA] with n hn
    have hv : min (A*x n) 1∈Icc (0:ℝ) 1 :=
      ⟨le_min (mul_nonneg hA.le (hxp n).le) zero_le_one,min_le_right _ _⟩
    have H := quantileMassProfile_le_of_larger_clock (M n).sweepRadius
      (((M n).sweepRadius_monotone).monotoneOn _)

      (fun u _=>(M n).sweepRadius_bounds0 u) hv hn.2

    exact (div_le_iff₀ (hxp n)).mpr (H.trans (min_le_left _ _))
  have hbounded : ∀ᶠn in atTop,
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs≤ K*(M n).xs^2 := by
    filter_upwards [hwork] with n hn
    exact (div_le_iff₀ (pow_pos (M n).hxs 2)).mp hn
  obtain ⟨c,R0,B,hc,hR0,hB,Hcal⟩ :=
    exists_actual_selected_bad_history_bounded_strength_scalar_calibration_along_comparable_shrinking_original_q
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare K hK hbounded
  have hcal : ∀ᶠn in atTop,∃q,c*x n≤ q ∧ q≤ R0*x n ∧
      |scalarCovarianceResponse hT (alpha n) (T*q)-q|≤ B*(x n)^3 := by
    filter_upwards [Hcal] with n hn
    obtain ⟨ht,q,hq⟩ := hn
    exact ⟨q,hq⟩
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩ :=
    comparison_local_joint_scalar_radius_compactness hT hTemp hR0 hc hB alpha radiusCDF x hx hxp
      (fun n q=>(M n).inheritedScalarMassProfile_right_continuous hT (htotal n) q)
      hcap hradiusCap hcal
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
    omitted_small := G.omission_over_test_zero_original_q.comp hphi.tendsto_atTop
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
  exact actual_selected_bad_history_bounded_strength_support_zero_along_comparable_shrinking_original_q K hK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp_original_q phi hphi) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n))
    (hphi.tendsto_atTop.eventually hwork) (fun n=>htotal (phi n))
    V.mass g ht hRt (fun a _=>hV a) (fun e he _=>hsupport e he) (fun R hR=>(Hphysical R hR).2.2) Hcontinuous

theorem exists_actual_selected_bad_history_bounded_joint_scalar_limit_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        Nonempty (ActualOriginalQLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal)  := by
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp G.total_root_bare_original_q
  let shift:=fun n : ℕ=>n+n0
  have hshift : StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij n0
  have ht0 : ∀n,∀u∈Icc (0:ℝ) 1,(M (shift n)).h u+(M (shift n)).b u ≤ T:=
    fun n=>(Hn0 (n+n0) (Nat.le_add_left n0 n)).1
  obtain ⟨psi,hpsi,Hlimit⟩:=exists_actual_selected_bad_history_bounded_joint_scalar_limit_of_total_along_comparable_shrinking_original_q K hK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (shift n)) (hdim.comp hshift.tendsto_atTop) (fun n=>M (shift n))
    (G.comp_original_q shift hshift) (fun n=>W (shift n)) (fun n=>hcanonical (shift n))
    (hWlim.comp hshift.tendsto_atTop) (fun n=>hcompare (shift n)) (hshift.tendsto_atTop.eventually hwork) ht0
  exact ⟨shift ∘ psi,hshift.comp hpsi,fun n=>ht0 (psi n),Hlimit⟩

theorem exists_actual_selected_bad_history_high_strength_scalar_calibration_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
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
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_original_q
      b hbpos hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
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

theorem exists_actual_selected_bad_history_high_scalar_compactness_of_total_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
 :
    let hT := G.hT
    let alpha := fun n=>(M n).inheritedScalarMassProfileBare hT (htotal n)
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
  let alpha := fun n=>(M n).inheritedScalarMassProfileBare hT (htotal n)
  let radiusCDF := fun n=>(M n).actualRadiusMassProfile
  let x := fun n=>(M n).xs
  have hxp : ∀n,0<x n := fun n=>(M n).hxs
  have hx : Tendsto x atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hcaps := actual_comparable_context_original_scalar_cdf_caps_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G htotal
  have hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤ A ∧
      ∀ᶠn in atTop,(alpha n).val ((T/T)*(x n*R))≤ A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩ := Hcaps.2 R hR
    exact ⟨A,hA.le,HA.mono fun n hn=>hn (htotal n)⟩
  have hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠn in atTop,(radiusCDF n).val (x n*R)/x n≤ A := by
    intro R hR
    obtain ⟨A,hA,HA,_⟩ :=
      actual_comparable_context_compact_original_scalar_cuts_original_q
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M G htotal R hR
    refine ⟨A,?_⟩
    filter_upwards [HA] with n hn
    have hv : min (A*x n) 1∈Icc (0:ℝ) 1 :=
      ⟨le_min (mul_nonneg hA.le (hxp n).le) zero_le_one,min_le_right _ _⟩
    have H := quantileMassProfile_le_of_larger_clock (M n).sweepRadius
      (((M n).sweepRadius_monotone).monotoneOn _)

      (fun u _=>(M n).sweepRadius_bounds0 u) hv hn.2

    exact (div_le_iff₀ (hxp n)).mpr (H.trans (min_le_left _ _))
  obtain ⟨c,R0,B,hc,hR0,hB,Hcal⟩ :=
    exists_actual_selected_bad_history_high_strength_scalar_calibration_along_comparable_shrinking_original_q
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hlarge
  have hcal : ∀ᶠn in atTop,∃q,c*x n≤ q ∧ q≤ R0*x n ∧
      |scalarCovarianceResponse hT (alpha n) (T*q)-q|≤ B*(x n)^3 := by
    filter_upwards [Hcal] with n hn
    obtain ⟨ht,q,hq⟩ := hn
    exact ⟨q,hq⟩
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩ :=
    comparison_local_joint_scalar_radius_compactness hT hTemp hR0 hc hB alpha radiusCDF x hx hxp
      (fun n q=>(M n).inheritedScalarMassProfile_right_continuous hT (htotal n) q)
      hcap hradiusCap hcal
  exact ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩

theorem actual_selected_bad_history_high_strength_response_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*(M n).xs)
    (g : ℝ→ℝ)
    (hG : ∀Rclock > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let hT:=G.hT
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let G:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfileBare hT (htotal n)))
        T (M n).xs
    let q:=fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf z/(T*(M n).xs)
    (∀n,Integrable (fun z=>G n (q n z)) (nu n)) ∧
      Tendsto (fun n=>∫z,|G n (q n z)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun z=>q n z-(M n).sweepRadius z/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫z,|q n z-(M n).sweepRadius z/(M n).xs|∂nu n) atTop (𝓝 0) := by
  exact actual_comparable_context_shrinking_full_HIGH_response_original_q C hC hm hdelta hroom hcl hcu hAz hC0 hCt
    hCcal hc0 hc01 hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
    hlarge htotal v hv hvc g hG hg

theorem actual_selected_bad_history_high_strength_support_zero_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (V g : ℝ→ℝ) {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (hV : ∀a ≤ R,Tendsto (fun n=>(quantileMassProfile (M n).sweepRadius
      (fun u _=>(M n).sweepRadius_bounds0 u)).val

          ((M n).xs*a)/(M n).xs) atTop (𝓝 (V a)))
    (hsupport : ∀e : ℝ,0 < e→t+e < R→V (t-e) < V (t+e))
    (hG : ∀Rclock : ℝ,0<Rclock→ TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
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
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (hxspos n).le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*(M n).xs:=min_le_left _ _
  have hcut : ∀ᶠn in atTop,(M n).xs*R < (M n).sweepRadius (v n):=by
    have Hsmall : ∀ᶠn in atTop,C*(M n).xs ≤ 1:=by
      have H:=hxlim.const_mul C
      simpa only [mul_zero] using H.eventually (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
    filter_upwards [Hsmall,G.positive_bands_high_original_q C hC] with n hn hnhigh
    dsimp only [v]
    rw [min_eq_left hn]
    have HR:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (hxspos n) le_rfl hCband hn hnhigh (show C*(M n).xs∈Icc (C*(M n).xs) (C*(M n).xs) from
        ⟨le_rfl,le_rfl⟩)).1
    have H:=mul_lt_mul_of_pos_right hRC (hxspos n)
    exact (show (M n).xs*R < (C/cu)*(M n).xs by nlinarith only [H]).trans_le HR
  have Hresponse:=actual_selected_bad_history_high_strength_response_along_comparable_shrinking_original_q
    C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare hlarge htotal v hv hvc g hG hg
  have Hmass:=comparison_actual_radius_cdf_support_mass (fun n=>(M n).sweepRadius)
    (fun n=>(M n).xs) v V
    (fun n=>((M n).sweepRadius_monotone).monotoneOn _)

    (fun n u _=>(M n).sweepRadius_bounds0 u)

    hxspos hv hcut hV htR hsupport
  exact comparison_scalar_zero_of_positive_mass_on_compact
    (fun n=>comparisonNormalizedClockMass (M n).xs (v n)) (fun _=>inferInstance)
    (fun n (z : ParisiFinite.OrderPoint)=>(M n).sweepRadius z/(M n).xs)
    (fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf z/(T*(M n).xs))
    _ g ht htR
    (fun n=>(((M n).sweepRadius_continuous).measurable.comp

        measurable_subtype_coe).div_const _)
    (fun n=>(Hresponse.1 n).abs) (fun n=>(Hresponse.2.2.1 n).abs)
    Hresponse.2.1 Hresponse.2.2.2 Hmass (hG R (ht.trans htR))
    ((hg R (ht.trans htR)).continuousAt (Icc_mem_nhds ht htR))

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_of_total_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧ Nonempty
      (ActualOriginalQLocalScalarLimitData (G.hT)
        T (fun n=>M (phi n)) (fun n=>htotal (phi n))) := by
  have hTemp : 0 < T := G.hT
  let hT : 0<T := G.hT
  let alpha := fun n=>(M n).inheritedScalarMassProfileBare hT (htotal n)
  let x := fun n=>(M n).xs
  obtain ⟨beta,radiusLimit,U,V,sigma,phi,hphi,halpha,hradius,hU,hV,Hlimits⟩ :=
    exists_actual_selected_bad_history_high_scalar_compactness_of_total_along_comparable_shrinking_original_q
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
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
    omitted_small := G.omission_over_test_zero_original_q.comp hphi.tendsto_atTop
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
  exact actual_selected_bad_history_high_strength_support_zero_along_comparable_shrinking_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp_original_q phi hphi) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n))
    (hlarge.comp hphi.tendsto_atTop) (fun n=>htotal (phi n))
    V.mass g ht hRt (fun a _=>hV a) (fun e he _=>hsupport e he) (fun R hR=>(Hphysical R hR).2.2) Hcontinuous

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_along_comparable_shrinking_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        Nonempty (ActualOriginalQLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal)  := by
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp G.total_root_bare_original_q
  let shift:=fun n : ℕ=>n+n0
  have hshift : StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij n0
  have ht0 : ∀n,∀u∈Icc (0:ℝ) 1,(M (shift n)).h u+(M (shift n)).b u ≤ T:=
    fun n=>(Hn0 (n+n0) (Nat.le_add_left n0 n)).1
  obtain ⟨psi,hpsi,Hlimit⟩:=exists_actual_selected_bad_history_high_joint_scalar_limit_of_total_along_comparable_shrinking_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (shift n)) (hdim.comp hshift.tendsto_atTop) (fun n=>M (shift n))
    (G.comp_original_q shift hshift) (fun n=>W (shift n)) (fun n=>hcanonical (shift n))
    (hWlim.comp hshift.tendsto_atTop) (fun n=>hcompare (shift n)) (hlarge.comp hshift.tendsto_atTop) ht0
  exact ⟨shift ∘ psi,hshift.comp hpsi,fun n=>ht0 (psi n),Hlimit⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
