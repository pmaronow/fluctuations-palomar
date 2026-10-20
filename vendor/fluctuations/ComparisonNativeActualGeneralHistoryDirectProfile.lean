module

public import ComparisonNativeActualHistoryCompleteDirectProfileAlong
public import ComparisonNativeActualGeneralHistoryCavityBackend
public import ComparisonNativeActualGeneralHistoryContext
public import ComparisonNativeActualGeneralHistoryRadiusConcentration

@[expose] public section

noncomputable section
set_option linter.unusedVariables false

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_bounded_strength_scalar_calibration_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
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
          |scalarCovarianceResponse (G.hT)
            ((M n).inheritedScalarMassProfile (G.hT) htotal)
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
  obtain ⟨ps,Hps⟩ := G.literal_readout
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
    filter_upwards [Hps] with n hn
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha T (G.epsilon n) (G.shell n) ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
      (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl
  obtain ⟨Cs,hCs,Hband⟩ := eventually_actual_regular_calibrated_mass_band
    hm hdelta hroom hcl hcu hAz hC0 hCt (L:=1) (by norm_num)
    dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl) hxlim Hclock
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_weak_general
      b hbpos hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have Hnear := actual_selected_bad_shell_history_near_bare_clocks_weak_general
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G (fun n=>(M n).xs)
    (Eventually.of_forall (fun _=>le_rfl)) hxlim b 1 hbpos.le zero_lt_one
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
        c*(M n).xs ≤ orderedPathS (dim n+1) (M n).bf (M n).hf u ∧
        orderedPathS (dim n+1) (M n).bf (M n).hf u ≤ Cs*(M n).xs ∧
        (a/cu)*(M n).xs ≤ (M n).R u ∧ (M n).R u ≤ (b/cl)*(M n).xs ∧
        (M n).xs ≤ (M n).R u ∧ (M n).z ≤ (M n).R u/2 := by
    simpa only [a,b,c,mul_one] using ⟨hnBand.2.1,hnBand.2.2.1⟩
  let f := (M n).inheritedScalarCavityResidual
    (G.hT) htotal
  have hfi : IntervalIntegrable f volume 0 (b*(M n).xs) :=
    (M n).original_scalar_gap_intervalIntegrable
      (G.hT)
      ((M n).inheritedScalarMassProfile (G.hT) htotal)
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
      T*orderedPathS (dim n+1) (M n).bf (M n).hf u| ≤ Ck*(M n).xs^3 := by
    simpa only [one_mul,Ck] using (M n).inherited_clock_cubic_error_of_eq4
      hu01 (M n).hxs.le (show (0:ℝ) ≤ 1 by norm_num) hKstrength
      Hnear.1 Hnear.2 he hmismatch hShi
  refine ⟨htotal,actualMixedClock (dim n+1) (M n).bf (M n).hf u/T,?_⟩
  exact scalar_calibration_at_local_temperature
    (scalarCovarianceResponse (G.hT)
      ((M n).inheritedScalarMassProfile (G.hT) htotal))
    hTemp (M n).hxs hnUnit hCk hSlo hShi hclock hnSmall
    (show |orderedPathS (dim n+1) (M n).bf (M n).hf u-
      scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) htotal)
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤ 1*(M n).xs^3 by
      simpa only [one_mul,f,inheritedScalarCavityResidual] using hres)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_initial_mismatch_clock_regularity_weak_general
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M Temp c0) :
    ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
  exact G.pullback

theorem actual_selected_bad_history_initial_mass_squared_mismatch_ratio_tendsto_zero_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M Temp c0)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0) := by
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity_weak_general dim M
    G
  exact regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim Hclock C hC

theorem actual_selected_bad_history_initial_mass_absolute_mismatch_ratio_tendsto_zero_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M Temp c0)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity_weak_general dim M
    G
  exact regular_minimum_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim Hclock C hC

theorem actual_selected_bad_history_original_retained_squared_mismatch_ratio_tendsto_zero_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M Temp c0)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*W n) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^3) atTop (𝓝 0) := by
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity_weak_general dim M
    G
  exact regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W v hxs hWlim Hclock C hC hv hvc

theorem actual_selected_bad_history_initial_mass_squared_mismatch_at_working_scale_tendsto_zero_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M Temp c0)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/((M n).xs)^3)
      atTop (𝓝 0) := by
  have Hxs:Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=
    squeeze_zero (fun n=>(M n).hxs.le)
      (fun n=>(M n).canonical_direct_test_band_ge_scale) hcanonical
  exact actual_selected_bad_history_initial_mass_squared_mismatch_ratio_tendsto_zero_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
    (fun _=>le_rfl) Hxs G C hC

theorem actual_selected_bad_history_original_retained_squared_mismatch_at_working_scale_tendsto_zero_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock Temp c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : ℕ→ℝ)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M Temp c0)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*(M n).xs) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/((M n).xs)^3) atTop (𝓝 0) := by
  have Hxs:Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=
    squeeze_zero (fun n=>(M n).hxs.le)
      (fun n=>(M n).canonical_direct_test_band_ge_scale) hcanonical
  exact actual_selected_bad_history_original_retained_squared_mismatch_ratio_tendsto_zero_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs) v
    (fun _=>le_rfl) Hxs G C hC hv hvc

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_local_temperature_initial_scalar_radius_coupling_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |actualMixedClock (dim n+1) (M n).bf (M n).hf u/T-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  have hlocal : 0 < T := G.hT
  have hT:0 < T:=G.hT
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity_weak_general
    dim M G
  have Htotal:=actual_selected_bad_history_total_clock_and_root_weak_general
    dim M G
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks_weak_general
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G W (Eventually.of_forall hxs) hWlim
  have Hcouple:=regular_initial_local_temperature_scalar_radius_coupling_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim Hclock hT hlocal
    (Htotal.mono fun _ hn=>hn.1) C 1 1 hC (by norm_num) (by norm_num)
    (Hnear C 1 hC.le (by norm_num))
  apply Hcouple.congr'
  filter_upwards [Htotal] with n hn
  have hCW:0 ≤ C*W n:=mul_nonneg hC.le ((M n).hxs.trans_le (hxs n)).le
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hCW] at hu
  dsimp only
  rw [(M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root T hn.2 hu.1]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0) :
    ∀R > 0,∃C : ℝ,0 < C ∧
      (∀ᶠn in atTop,W n*R < actualMixedClock (dim n+1) (M n).bf (M n).hf (min (C*W n) 1)/T ∧
        W n*R < (M n).R (min (C*W n) 1)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ min (C*W n) 1},
        |actualMixedClock (dim n+1) (M n).bf (M n).hf w/T-(M n).R w|
          ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^2) atTop (𝓝 0) := by
  have hlocal : 0 < T := G.hT
  intro R hR
  let C:=max (2*starMassBandConstant cu Az) (2*cu*(R+1))
  have hA : starMassBandConstant cu Az ≤ C/2 := by dsimp [C];linarith [le_max_left (2*starMassBandConstant cu Az) (2*cu*(R+1))]
  have hRC : R+1 ≤ (C/2)/cu := (le_div_iff₀ hcu).mpr (by
    dsimp [C];nlinarith only [le_max_right (2*starMassBandConstant cu Az) (2*cu*(R+1))])
  have hC : 0 < C := by have H:=star_mass_band_constant_pos hcu hAz;linarith
  have Hcouple:=actual_selected_bad_history_local_temperature_initial_scalar_radius_coupling_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin dim hdim
    M W hxs hWlim G C hC
  have Hroot:=actual_selected_bad_history_total_clock_and_root_weak_general
    dim M G
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have Hsmall:=Hcouple.eventually (eventually_lt_nhds (show (0:ℝ) < C/2 by positivity))
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  refine ⟨C,hC,?_,?_⟩
  · filter_upwards [HW,Hsmall,Hroot] with n hnW hnsmall hnRoot
    have hw:=hW n
    rw [min_eq_left hnW]
    have hv : C*W n∈Icc (0:ℝ) 1 := ⟨by positivity,hnW⟩
    have hs : (C/2)*W n∈Icc (0:ℝ) (C*W n) := ⟨by positivity,by nlinarith [hW n]⟩
    have Hrad:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (hW n) (hxs n) hA (hs.2.trans hnW) (show (C/2)*W n∈Icc ((C/2)*W n) ((C/2)*W n) from ⟨le_rfl,le_rfl⟩)).1
    have Hrise : W n*R+W n ≤ (M n).R ((C/2)*W n) := by
      nlinarith only [Hrad,mul_le_mul_of_nonneg_right hRC (hW n).le]
    have Hint : (∫u in 0..C*W n,|actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf u-(M n).R u|) <
        W n*(C*W n-(C/2)*W n) := by
      have H:=(div_lt_iff₀ (pow_pos (hW n) 2)).mp hnsmall
      have Heq : (∫u in 0..C*W n,
          |actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf u-(M n).R u|)=
          ∫u in 0..C*W n,|actualMixedClock (dim n+1) (M n).bf (M n).hf u/T-(M n).R u| := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hv.1] at hu
        dsimp only
        rw [(M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root T hnRoot.2 hu.1]
      rw [Heq]
      convert H using 1;ring
    have Hq:=monotone_scalar_cut_of_original_integral _ _
      (actualScalarClockQuantile_monotone hlocal (dim n+1) (by omega) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone)
      ((comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk (M n).context.hkc
        (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
      hv hs Hrise ((M n).inherited_scalar_radius_intervalIntegrable hlocal hv) Hint
    have HRmono:=(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha) hs.2
    rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf (by positivity : 0<C*W n)] at Hq
    exact ⟨Hq,by linarith [hW n]⟩
  · apply Hcouple.congr'
    filter_upwards [HW] with n hnW
    have hw:=hW n
    rw [min_eq_left hnW,comparison_original_retained_integral_eq_interval
      (show C*W n∈Icc (0:ℝ) 1 from ⟨by positivity,hnW⟩)
      (fun u=>|actualMixedClock (dim n+1) (M n).bf (M n).hf u/T-(M n).R u|)]

theorem actual_selected_bad_history_local_temperature_original_scalar_cdf_caps_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0) :
    (∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧
    ∀R > 0,∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
      ((M n).inheritedScalarMassProfile (G.hT) htotal).val
        ((T/T)*(W n*R)) ≤ C*W n := by
  have hlocal : 0 < T := G.hT
  have hT:0 < T:=G.hT
  refine ⟨(actual_selected_bad_history_total_clock_and_root_weak_general
    dim M G).mono (fun _ hn=>hn.1),?_⟩
  intro R hR
  obtain ⟨C,hC,Hcut,_⟩:=actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin dim hdim
    M W hxs hWlim G R hR
  refine ⟨C,hC,?_⟩
  filter_upwards [Hcut] with n hn
  intro htotal
  have hW:0 < W n:=(M n).hxs.trans_le (hxs n)
  have hv:min (C*W n) 1∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le hW.le) zero_le_one,min_le_right _ _⟩
  have hv0:0 < min (C*W n) 1:=lt_min (mul_pos hC hW) zero_lt_one
  have Hamb:(T/T)*(W n*R) <
      actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf (min (C*W n) 1) := by
    rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf hv0]
    have H:=mul_lt_mul_of_pos_left hn.1 (div_pos hlocal hT)
    convert H using 1; field_simp [hlocal.ne',hT.ne']
  have H:=quantileMassProfile_le_of_larger_clock
    (actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf)
    (actualScalarClockQuantile_monotone hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone)
    (actualScalarClockQuantile_bounds hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone ((M n).inherited_total_clock_le htotal))
    hv Hamb
  exact H.trans (min_le_left _ _)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology ENNReal
set_option maxHeartbeats 12000000

theorem exists_actual_selected_bad_history_normalized_scalar_gap_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
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
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_weak_general
      Atarget hAtarget hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨eta,heta,hetalim,
    actual_original_scalar_gap_normalized_envelope_along
      (G.hT) hAtarget eta M hxlim Hgap,?_⟩
  intro htotal v hv hvA
  exact actual_original_scalar_gap_normalized_l1_tendsto_zero_along
    (G.hT) hAtarget eta hetalim M htotal hxlim Hgap v hv hvA

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem actual_selected_bad_history_bounded_strength_response_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C K : ℝ) (hC : 0 < C) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*(M n).xs) :
    let hT:=G.hT
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let G:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n)))
        T (M n).xs
    let q:=fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/(T*(M n).xs)
    (∀n,Integrable (fun z=>G n (q n z)) (nu n)) ∧
      Tendsto (fun n=>∫z,|G n (q n z)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun z=>q n z-(M n).R z/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫z,|q n z-(M n).R z/(M n).xs|∂nu n) atTop (𝓝 0) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨_eta,_heta,_hetalim,_Henvelope,Hcavity⟩:=
    exists_actual_selected_bad_history_normalized_scalar_gap_along_weak_general
      C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have Hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity_weak_general
    dim M G
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks_weak_general
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G (fun n=>(M n).xs)
    (Eventually.of_forall fun _=>le_rfl) Hxs
  have Hbare : ∀eps > 0,∀ᶠn in atTop,∀z : ParisiFinite.OrderPoint,z.val ≤ v n →
      |(M n).b z-T| ≤ eps*(M n).xs^2 ∧
        |(M n).h z| ≤ eps*(M n).xs^3 := by
    intro eps heps
    filter_upwards [Hnear C eps hC.le heps] with n hn
    intro z hz
    exact hn z ⟨z.property.1,hz.trans (hvc n)⟩
  have Hcav:=Hcavity htotal v hv (Eventually.of_forall hvc)
  exact actual_inherited_local_temperature_restricted_response_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
    (fun _=>le_rfl) Hxs Hclock hTemp (G.hT) htotal
    (fun n=>{z : ParisiFinite.OrderPoint | (z:ℝ) ≤ v n})
    (fun _=>measurableSet_le measurable_subtype_coe measurable_const)
    C K hC hK (fun n z hz=>hz.trans (hvc n)) hwork Hbare Hcav.1 Hcav.2

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem actual_selected_bad_history_bounded_strength_support_zero_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (V g : ℝ→ℝ) {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (hV : ∀a ≤ R,Tendsto (fun n=>(quantileMassProfile (M n).R
      (fun u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)).val
          ((M n).xs*a)/(M n).xs) atTop (𝓝 (V a)))
    (hsupport : ∀e : ℝ,0 < e→t+e < R→V (t-e) < V (t+e))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) R))
    (hg : ContinuousAt g t) : g t=0 := by
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
  have Hresponse:=actual_selected_bad_history_bounded_strength_response_along_weak_general
    C K hC hK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare hwork htotal v hv hvc
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
    Hresponse.2.1 Hresponse.2.2.2 Hmass hG hg

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_joint_scalar_limit_of_total_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧ Nonempty
      (ActualInheritedLocalScalarLimitData (G.hT)
        T (fun n=>M (phi n)) (fun n=>htotal (phi n))) := by
  have hTemp : 0 < T := G.hT
  let hT : 0<T := G.hT
  let alpha := fun n=>(M n).inheritedScalarMassProfile hT (htotal n)
  let radiusCDF := fun n=>(M n).actualRadiusMassProfile
  let x := fun n=>(M n).xs
  have hxp : ∀n,0<x n := fun n=>(M n).hxs
  have hx : Tendsto x atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hcaps := actual_selected_bad_history_local_temperature_original_scalar_cdf_caps_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M x (fun _=>le_rfl) hx G
  have hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠn in atTop,(alpha n).val ((T/T)*(x n*R))≤A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩ := Hcaps.2 R hR
    exact ⟨A,hA.le,HA.mono fun n hn=>hn (htotal n)⟩
  have hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠn in atTop,(radiusCDF n).val (x n*R)/x n≤A := by
    intro R hR
    obtain ⟨A,hA,HA,_⟩ :=
      actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along_weak_general
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M x (fun _=>le_rfl) hx G R hR
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
    exists_actual_selected_bad_history_bounded_strength_scalar_calibration_along_weak_general
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare K hK hbounded
  have hcal : ∀ᶠn in atTop,∃q,c*x n≤q ∧ q≤R0*x n ∧
      |scalarCovarianceResponse hT (alpha n) (T*q)-q|≤B*(x n)^3 := by
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
  exact actual_selected_bad_history_bounded_strength_support_zero_along_weak_general K hK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n))
    (hphi.tendsto_atTop.eventually hwork) (fun n=>htotal (phi n))
    V.mass g ht hRt (fun a _=>hV a) (fun e he _=>hsupport e he) H.2.2 hg

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_joint_scalar_limit_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
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
  obtain ⟨psi,hpsi,Hlimit⟩:=exists_actual_selected_bad_history_bounded_joint_scalar_limit_of_total_along_weak_general K hK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (shift n)) (hdim.comp hshift.tendsto_atTop) (fun n=>M (shift n))
    (G.comp shift hshift) (fun n=>W (shift n)) (fun n=>hcanonical (shift n))
    (hWlim.comp hshift.tendsto_atTop) (fun n=>hcompare (shift n)) (hshift.tendsto_atTop.eventually hwork) ht0
  exact ⟨shift ∘ psi,hshift.comp hpsi,fun n=>ht0 (psi n),Hlimit⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_scalar_strength_spin_limit_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
      Nonempty (ActualInheritedLocalScalarLimitData
        (G.hT) T
        (fun n=>M (phi n)) htotal) ∧
      ∃(L A B : ℝ) (s : NonnegativeMassProfile),
      L∈Icc (1/Ccal^2) (K+1) ∧ A∈Icc (0:ℝ) Ccal ∧ 0 < B ∧
      (∀t : ℝ,Tendsto (fun n=>laplaceComparisonStrength (M (phi n)).context.d
        (M (phi n)).lam ((M (phi n)).xs*t)/(M (phi n)).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t)))) ∧
      (∀t : ℝ,Tendsto (fun n=>comparisonLogSlope
        (laplaceComparisonStrength (M (phi n)).context.d (M (phi n)).lam)
        ((M (phi n)).xs*t)) atTop (𝓝 (laplaceComparisonSlope (A*t)))) ∧
      (∀t : ℝ,0 < L*laplaceComparisonShape (A*t) ∧ laplaceComparisonSlope (A*t)∈Ico (0:ℝ) 1) ∧
      (∀t : ℝ,0 ≤ t → s.mass t ≤ B*(1+t)) ∧
      ∀t : ℝ,0 ≤ t → Tendsto (fun n=>orderedPathS (dim (phi n)+1)
        (M (phi n)).bf (M (phi n)).hf ((M (phi n)).xs*t)/(M (phi n)).xs)
        atTop (𝓝 (s.mass t)) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨theta,htheta,htotal,⟨d⟩⟩ :=
    exists_actual_selected_bad_history_bounded_joint_scalar_limit_along_weak_general K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hwork
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨L,A,B,s,psi,hpsi,hL,hA,hB,HL,HA,Hpositive,Hsbound,Hs⟩ :=
    exists_actual_bounded_strength_spin_profile_limits K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal (fun n=>dim (theta n))
      (hdim.comp htheta.tendsto_atTop) (fun n=>M (theta n)) (hx.comp htheta.tendsto_atTop)
      (fun n=>hcompare (theta n)) (htheta.tendsto_atTop.eventually hwork)
  exact ⟨theta ∘ psi,htheta.comp hpsi,fun n=>htotal (psi n),⟨d.comp psi hpsi⟩,
    L,A,B,s,hL,hA,hB,HL,HA,Hpositive,Hsbound,Hs⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_scalar_strength_radius_spin_limit_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
      Nonempty (ActualInheritedLocalScalarLimitData
        (G.hT) T
        (fun n=>M (phi n)) htotal) ∧
      ∃(L A B : ℝ) (s : NonnegativeMassProfile),
      L∈Icc (1/Ccal^2) (K+1) ∧ A∈Icc (0:ℝ) Ccal ∧ 0 < B ∧
      (∀t : ℝ,Tendsto (fun n=>laplaceComparisonStrength (M (phi n)).context.d
        (M (phi n)).lam ((M (phi n)).xs*t)/(M (phi n)).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t)))) ∧
      (∀t : ℝ,Tendsto (fun n=>comparisonLogSlope
        (laplaceComparisonStrength (M (phi n)).context.d (M (phi n)).lam)
        ((M (phi n)).xs*t)) atTop (𝓝 (laplaceComparisonSlope (A*t)))) ∧
      (∀t : ℝ,0 < L*laplaceComparisonShape (A*t) ∧ laplaceComparisonSlope (A*t)∈Ico (0:ℝ) 1) ∧
      (∀t : ℝ,0 ≤ t → s.mass t ≤ B*(1+cu*(t+Az))) ∧
      ∀t : ℝ,Tendsto (fun n=>orderedPathS (dim (phi n)+1)
        (M (phi n)).bf (M (phi n)).hf
          ((M (phi n)).alpha.val.val ((M (phi n)).xs*t))/(M (phi n)).xs)
        atTop (𝓝 (s.mass t)) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨theta,htheta,htotal,⟨d⟩,L,A,_B,_smass,hL,hA,_hB,HL,HA,Hpositive,_Hbound,_Hs⟩ :=
    exists_actual_selected_bad_history_bounded_scalar_strength_spin_limit_along_weak_general K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hwork
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨s,B,psi,hB,hpsi,Hsbound,Hs⟩ := exists_actual_rescaled_radius_spin_profile_limit
    hm hdelta hroom hcl hcu hAz hC0 hCt (fun n=>dim (theta n))
    (hdim.comp htheta.tendsto_atTop) (fun n=>M (theta n)) (hx.comp htheta.tendsto_atTop)
  refine ⟨theta ∘ psi,htheta.comp hpsi,fun n=>htotal (psi n),⟨d.comp psi hpsi⟩,
    L,A,B,s,hL,hA,hB,?_,?_,Hpositive,Hsbound,Hs⟩
  · intro t
    exact (HL t).comp hpsi.tendsto_atTop
  · intro t
    exact (HA t).comp hpsi.tendsto_atTop

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum

theorem actual_selected_bad_history_compact_radius_thermal_L1_along_weak_general
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C a b : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (ha : 0 ≤ a) (hab : a ≤ b)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    Tendsto (fun n=>∫t in Icc a b,
      (M n).cavityRadiusPointDefect ((M n).xs*t)/(M n).xs^2) atTop (𝓝 0) := by
  let Cbig := max C b
  have Hlim := actual_selected_bad_history_radius_strip_thermal_tendsto_zero_along_weak_general
    (C:=Cbig) Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hc
    dim hdim M hxs G
  have hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have he n := comparison_radius_rescaling_integral
    (M n).cavityRadiusPointDefect hab (M n).hxs
  apply squeeze_zero' _ _ Hlim
  · filter_upwards [hsmall] with n hn
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg ((M n).cavityRadiusPointDefect_nonneg
      ⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),
        (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hn⟩) (sq_nonneg _)
  · filter_upwards [hsmall,hmass] with n hn hmn
    rw [he n]
    apply div_le_div_of_nonneg_right _ (pow_nonneg (M n).hxs.le 3)
    have hsub : Icc ((M n).xs*a) ((M n).xs*b) ⊆
        (M n).actualRadiusTargetStrip c Cbig := by
      intro r hr
      have ht : r/(M n).xs∈Icc a b :=
        ⟨(le_div_iff₀ (M n).hxs).mpr (by simpa only [mul_comm] using hr.1),
          (div_le_iff₀ (M n).hxs).mpr (by simpa only [mul_comm] using hr.2)⟩
      have H := hmn (r/(M n).xs) ht
      rw [mul_div_cancel₀ r (M n).hxs.ne'] at H
      refine ⟨⟨(mul_nonneg (M n).hxs.le ha).trans hr.1,
        le_min ?_ (hr.2.trans hn)⟩,H.1,?_⟩
      · exact hr.2.trans (by simpa only [Cbig,mul_comm] using
          mul_le_mul_of_nonneg_left (le_max_right C b) (M n).hxs.le)
      · exact H.2.trans (mul_le_mul_of_nonneg_right (le_max_left C b) (M n).hxs.le)
    have hi := (M n).cavity_radius_point_defect_unit_integrable.mono_set
      (show (M n).actualRadiusTargetStrip c Cbig ⊆ Icc (0:ℝ) 1 from
        fun r hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
    apply setIntegral_mono_set hi _ (Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem ((M n).actual_radius_target_strip_measurable c Cbig)] with r hr
    exact (M n).cavityRadiusPointDefect_nonneg ⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 12000000

theorem actual_selected_bad_history_bounded_radius_gradient_L1_along_weak_general
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D T c0 c C a b K L A : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) (hK : 0 ≤ K)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0)
    (hwork : ∀ᶠn in atTop,
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2 ≤ K)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (s : NonnegativeMassProfile)
    (Hstrength : ∀t∈Icc a b,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
      atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hslope : ∀t∈Icc a b,Tendsto (fun n=>comparisonLogSlope
      (laplaceComparisonStrength (M n).context.d (M n).lam) ((M n).xs*t))
      atTop (𝓝 (laplaceComparisonSlope (A*t))))
    (Hspin : ∀t∈Icc a b,Tendsto (fun n=>(M n).actualScaledRadiusSpin t)
      atTop (𝓝 (s.mass t))) :
    Tendsto (fun n=>∫t in Icc a b,|(M n).actualVirtualScaledGradient t-
      comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
        (laplaceComparisonSlope (A*t)) t (s.mass t)|) atTop (𝓝 0) := by
  let F:=fun t=>comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
    (laplaceComparisonSlope (A*t)) t (s.mass t)
  have hFm : Measurable F := by
    have hs:=s.monotone.measurable
    have hh : Measurable (fun t:ℝ=>laplaceComparisonShape (A*t)) :=
      laplaceComparisonShape_contDiff.continuous.measurable.comp
      (measurable_const.mul measurable_id)
    have hp : Measurable (fun t:ℝ=>laplaceComparisonSlope (A*t)) :=
      comparison_shape_slope_continuous.measurable.comp
      (measurable_const.mul measurable_id)
    unfold F comparisonScaledStationarity
    fun_prop
  have hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  obtain ⟨B,hB,Hraw⟩:=eventually_actual_minimum_mass_mean_upper Bclock
    hm hdelta (by linarith) hcl hcu hAz hC0 hCt
  let Kbig:=max (K+1) (B*(1+C))
  have Hbounds : ∀ᶠn in atTop,∀t∈Icc a b,
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2∈Icc (0:ℝ) Kbig ∧
      comparisonLogSlope (laplaceComparisonStrength (M n).context.d (M n).lam)
        ((M n).xs*t)∈Icc (0:ℝ) 1 ∧ (M n).actualScaledRadiusSpin t∈Icc (0:ℝ) Kbig := by
    filter_upwards [hwork,hmass,hdim.eventually Hraw] with n hwn hmn hrn
    intro t ht
    have ham:=hmn t ht
    have hau:= (M n).alpha.val.property.1 ((M n).xs*t)
    have hap : 0 < (M n).alpha.val.val ((M n).xs*t) :=
      (mul_pos hc (M n).hxs).trans_le ham.1
    have Hmean:=hrn (M n) _ ⟨hap,hau.2⟩
    have Hspinb : (M n).actualScaledRadiusSpin t ≤ B*(1+C) := by
      apply (div_le_iff₀ (M n).hxs).mpr
      calc
        _ ≤ B*((M n).xs+(M n).alpha.val.val ((M n).xs*t)) := Hmean
        _ ≤ B*((M n).xs+C*(M n).xs) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl ham.2) hB.le
        _ = B*(1+C)*(M n).xs := by ring
    have Hstrengthb:=comparison_zero_strength_bound_of_working (M n).context.hd
      (M n).hlam.le (M n).hxs (M n).hld hK hwn
    have hp:=laplaceComparisonStrength_logSlope_mem (M n).context.hd.ne'
      (M n).hlam.ne' ((M n).xs*t)
    refine ⟨⟨div_nonneg (laplaceComparisonStrength_pos _ (M n).hlam _).le (sq_nonneg _),?_⟩,⟨hp.1,hp.2.le⟩,
      ⟨div_nonneg ((M n).mass_mean_nonneg hau) (M n).hxs.le,
        Hspinb.trans (le_max_right _ _)⟩⟩
    exact ((div_le_div_of_nonneg_right
      (laplaceComparisonStrength_le (M n).context.d (M n).hlam.le _) (sq_nonneg _)).trans
      Hstrengthb).trans (le_max_left _ _)
  have HP : Tendsto (fun n=>∫t in Icc a b,|(M n).actualScaledPrincipalGradient t-F t|)
      atTop (𝓝 0) := by
    obtain ⟨n0,Hn0⟩:=eventually_atTop.mp Hbounds
    apply (tendsto_add_atTop_iff_nat n0).mp
    apply comparison_principal_density_L1_tendsto
      (fun n t=>laplaceComparisonStrength (M (n+n0)).context.d (M (n+n0)).lam
        ((M (n+n0)).xs*t)/(M (n+n0)).xs^2)
      (fun n t=>comparisonLogSlope (laplaceComparisonStrength (M (n+n0)).context.d
        (M (n+n0)).lam) ((M (n+n0)).xs*t))
      (fun n=>(M (n+n0)).actualScaledRadiusSpin)
      (fun t=>L*laplaceComparisonShape (A*t)) (fun t=>laplaceComparisonSlope (A*t))
      s.mass (K:=Kbig) ha hab
    · intro n
      exact ((laplaceComparisonStrength_contDiff _ _).continuous.measurable.comp
        (measurable_const.mul measurable_id)).div_const _
    · intro n
      simp_rw [comparison_slope_scaled_parameter_identity (M (n+n0)).context.hd.ne'
        (M (n+n0)).hlam.ne']
      exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
    · intro n
      exact (M (n+n0)).actual_scaled_radius_spin_monotone.measurable
    · exact (laplaceComparisonShape_contDiff.continuous.measurable.comp
        (measurable_const.mul measurable_id)).const_mul L
    · exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
    · exact s.monotone.measurable
    · intro n t ht
      exact (Hn0 (n+n0) (by omega) t ht).1
    · intro n t ht
      exact (Hn0 (n+n0) (by omega) t ht).2.1
    · intro n t ht
      exact (Hn0 (n+n0) (by omega) t ht).2.2
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ⟨(Hstrength t ht).comp (tendsto_add_atTop_nat n0),
        (Hslope t ht).comp (tendsto_add_atTop_nat n0),
        (Hspin t ht).comp (tendsto_add_atTop_nat n0)⟩
  have HD:=actual_selected_bad_history_compact_radius_thermal_L1_along_weak_general Bclock
    hm hdelta hmargin hcl hcu hAz hC0 hCt hc ha.le hab dim hdim M hxs
    G hmass
  have Hlim : Tendsto (fun n=>(∫t in Icc a b,|(M n).actualScaledPrincipalGradient t-F t|)+
      ((K+1)/a)*(∫t in Icc a b,(M n).cavityRadiusPointDefect ((M n).xs*t)/(M n).xs^2))
      atTop (𝓝 0) := by simpa only [mul_zero,add_zero] using HP.add (HD.const_mul ((K+1)/a))
  apply squeeze_zero' (Eventually.of_forall (fun n=>integral_nonneg (fun t=>abs_nonneg _))) _ Hlim
  filter_upwards [Hbounds,hsmall,hwork] with n hbn hsn hwn
  let bound:=Kbig*(2*b+2*Kbig+Kbig^2/a)
  have hPi : IntegrableOn (M n).actualScaledPrincipalGradient (Icc a b) := by
    apply Integrable.of_bound (M n).actual_scaled_principal_gradient_measurable.aestronglyMeasurable bound
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (by simpa only [Real.norm_eq_abs,actualScaledPrincipalGradient,bound] using
      comparison_scaled_stationarity_bound ha ht (hbn t ht).1 (hbn t ht).2.1 (hbn t ht).2.2)
  have hFi : IntegrableOn F (Icc a b) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable bound
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply le_of_tendsto ((comparison_scaled_stationarity_tendsto
      (Hstrength t ht) (Hslope t ht) (Hspin t ht)).abs)
    filter_upwards [Hbounds] with j hj
    simpa only [Real.norm_eq_abs] using comparison_scaled_stationarity_bound ha ht
      (hj t ht).1 (hj t ht).2.1 (hj t ht).2.2
  have hDi:=(M n).actual_scaled_radius_defect_integrable ha.le hsn
  have H:=integral_mono_of_nonneg
    (Eventually.of_forall (fun t=>abs_nonneg ((M n).actualVirtualScaledGradient t-F t)))
    ((hPi.sub hFi).abs.add (hDi.const_mul ((K+1)/a))) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have he:=(M n).actual_scaled_gradient_error_bound ha hsn hK hwn ht
      have ht:=(abs_sub_le ((M n).actualVirtualScaledGradient t)
        ((M n).actualScaledPrincipalGradient t) (F t))
      dsimp only [Pi.add_apply,Pi.sub_apply]
      linarith only [he,ht])
  have hadd:=integral_add (hPi.sub hFi).abs (hDi.const_mul ((K+1)/a))
  simp only [Pi.add_apply,Pi.sub_apply] at H hadd
  rw [hadd,integral_const_mul] at H
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_radius_gradient_limit_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
      Nonempty (ActualInheritedLocalScalarLimitData
        (G.hT) T
        (fun n=>M (phi n)) htotal) ∧
      ∃(L A B : ℝ) (s : NonnegativeMassProfile),
      L∈Icc (1/Ccal^2) (K+1) ∧ A∈Icc (0:ℝ) Ccal ∧ 0 < B ∧
      (∀t : ℝ,Tendsto (fun n=>laplaceComparisonStrength (M (phi n)).context.d
        (M (phi n)).lam ((M (phi n)).xs*t)/(M (phi n)).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t)))) ∧
      (∀t : ℝ,Tendsto (fun n=>comparisonLogSlope
        (laplaceComparisonStrength (M (phi n)).context.d (M (phi n)).lam)
        ((M (phi n)).xs*t)) atTop (𝓝 (laplaceComparisonSlope (A*t)))) ∧
      (∀t : ℝ,0 < L*laplaceComparisonShape (A*t) ∧ laplaceComparisonSlope (A*t)∈Ico (0:ℝ) 1) ∧
      (∀t : ℝ,0 ≤ t → s.mass t ≤ B*(1+cu*(t+Az))) ∧
      (∀t : ℝ,Tendsto (fun n=>orderedPathS (dim (phi n)+1)
        (M (phi n)).bf (M (phi n)).hf
          ((M (phi n)).alpha.val.val ((M (phi n)).xs*t))/(M (phi n)).xs)
        atTop (𝓝 (s.mass t))) ∧
      ActualBoundedRadiusGradientLimit (fun n=>M (phi n)) L A s := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,hd,L,A,B,s,hL,hA,hB,HL,HA,Hpositive,Hbound,Hs⟩ :=
    exists_actual_selected_bad_history_bounded_scalar_strength_radius_spin_limit_along_weak_general K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hwork
  refine ⟨phi,hphi,htotal,hd,L,A,B,s,hL,hA,hB,HL,HA,Hpositive,Hbound,Hs,?_⟩
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  intro c C a b hc ha hab hmass
  have hxphi:=hx.comp hphi.tendsto_atTop
  refine ⟨?_,?_⟩
  · have H : Tendsto (fun n=>(M (phi n)).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul,Function.comp_apply] using hxphi.mul_const b
    filter_upwards [H.eventually (eventually_le_nhds zero_lt_one)] with n hn
    exact (M (phi n)).actual_scaled_gradient_integrable ha hn
  · exact actual_selected_bad_history_bounded_radius_gradient_L1_along_weak_general Bclock
      hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc ha hab hK
      (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
      (fun n=>M (phi n)) hxphi
      (G.comp phi hphi) (hphi.tendsto_atTop.eventually hwork) hmass s
      (fun t _=>HL t) (fun t _=>HA t) (fun t _=>Hs t)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_bounded_virtual_gap_primitive_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (_hc0 : 0 < c0) (_hc01 : c0 ≤ 1)
    (_hmargin : delta/4 < 3*m-99*delta) (_hcapmargin : 100*delta < (1:ℝ)/3+m)
    (_hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData (G.hT)
      T M htotal)
    (L A : ℝ) (s : NonnegativeMassProfile) (hL : 0 < L) (hA : 0 ≤ A)
    (Hstrength : ∀t,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
      atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hslope : ∀t,Tendsto (fun n=>comparisonLogSlope
      (laplaceComparisonStrength (M n).context.d (M n).lam) ((M n).xs*t))
      atTop (𝓝 (laplaceComparisonSlope (A*t))))
    (Hspin : ∀t,Tendsto (fun n=>(M n).actualScaledRadiusSpin t) atTop (𝓝 (s.mass t)))
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport d.V.mass)
    (hbsupport : b∈comparisonIncrementSupport d.V.mass)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) :
    ∃Kj : ℝ,1 ≤ Kj ∧ ∃j : ℝ→ℝ,Monotone j ∧
      (∀t∈Icc a b,j t∈Icc (1/Kj^2) (Kj^2)) ∧
      Nonempty (ComparisonPinnedGapPrimitive a b (fun t=>j t*
        comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
          (laplaceComparisonSlope (A*t)) t (s.mass t))) := by
  have hTemp : 0 < T := G.hT
  have hmass : 0 < d.V.mass ((a+b)/2) := comparison_increment_support_positive_cdf_after
    d.V.monotone d.radius_negative_axis_zero hasupport (by linarith)
  let c:=d.V.mass ((a+b)/2)/2
  have hc : 0 < c := half_pos hmass
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨KG,hKG,Hgradient⟩ := eventually_actual_bounded_strength_gradient_uniform_on_band_along
    K B hK ((ha.trans hab.le).trans hbB.le) hm hdelta hroom hcl hcu hAz hC0 hCt
    hCcal dim hdim M hx hcompare hwork
  let f:=fun t=>comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
    (laplaceComparisonSlope (A*t)) t (s.mass t)
  have hf : IntegrableOn f (Icc a b) := comparison_bounded_principal_density_integrable s hL.le hA ha
  apply actual_virtual_gap_primitive_of_gradient_limit_along hdelta hcu.le hAz hC0 (by linarith)
    dim hdim M hx d.V.mass d.V.monotone d.radius_inverse_cdf_limit ha hab hbB
    hasupport hbsupport hgap hmass f hf
    ⟨KG,hKG.le,Hgradient.mono (fun _ hn t ht _=>hn t ht)⟩
  intro u hu v hv huv
  have Hmass := actual_compact_gap_mass_band_along dim M d.V.mass d.V.monotone
    d.radius_inverse_cdf_limit hab hgap hmass hu hv
  exact actual_selected_bad_history_bounded_radius_gradient_L1_along_weak_general Bclock
    hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc (ha.trans_lt hu.1) huv hK
    dim hdim M hx G hwork Hmass s
    (fun t _=>Hstrength t) (fun t _=>Hslope t) (fun t _=>Hspin t)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 15000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_support_spin_selections_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Slocal c0 : ℝ} (hT : 0 < T)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData hT Slocal M htotal)
    (p : ℝ) (hp : ∀delta : ℝ,0 < delta → d.V.mass (p-delta) < d.V.mass (p+delta)) :
    ∃ns : ℕ → ℕ,Tendsto ns atTop atTop ∧ ∃w : ℕ → ParisiFinite.OrderPoint,
      Tendsto (fun j=>(M (ns j)).R (w j)/(M (ns j)).xs) atTop (𝓝 p) ∧
      Tendsto (fun j=>orderedPathS (dim (ns j)+1) (M (ns j)).bf (M (ns j)).hf
        (w j)/(M (ns j)).xs) atTop (𝓝 p) := by
  let R := p+1
  let C := starMassBandConstant cu Az+cu*(|R|+1)+1
  have hCbase := star_mass_band_constant_pos hcu hAz
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCband : starMassBandConstant cu Az ≤ C := by
    dsimp only [C]
    have H : 0 ≤ cu*(|R|+1) := by positivity
    linarith
  have hRC : R < C/cu := by
    apply (lt_div_iff₀ hcu).mpr
    dsimp only [C]
    have H := mul_le_mul_of_nonneg_right (le_abs_self R) hcu.le
    nlinarith
  let v := fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hsmall : ∀ᶠn in atTop,C*(M n).xs ≤ 1 := by
    have H := hx.const_mul C
    simpa only [mul_zero] using H.eventually (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have Hcut : ∀ᶠn in atTop,(M n).xs*R < (M n).R (v n) := by
    filter_upwards [Hsmall] with n hn
    dsimp only [v]
    rw [min_eq_left hn]
    have HR := ((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (M n).hxs le_rfl hCband hn
      (show C*(M n).xs∈Icc (C*(M n).xs) (C*(M n).xs) from ⟨le_rfl,le_rfl⟩)).1
    have H := mul_lt_mul_of_pos_right hRC (M n).hxs
    exact (show (M n).xs*R < (C/cu)*(M n).xs by nlinarith only [H]).trans_le HR
  let mu := fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let radius := fun n (w : ParisiFinite.OrderPoint)=>(M n).R w/(M n).xs
  let spin := fun n (w : ParisiFinite.OrderPoint)=>
    orderedPathS (dim n+1) (M n).bf (M n).hf w/(M n).xs
  have Hmass : ∀eps : ℝ,0 < eps → ∃c : ℝ,0 < c ∧
      ∀ᶠn in atTop,c ≤ (mu n).real {w | |radius n w-p| < eps} :=
    comparison_actual_radius_cdf_support_mass (fun n=>(M n).R) (fun n=>(M n).xs) v d.V.mass
      (fun n=>(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
      (fun n u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)
      (fun n=>(M n).hxs) hv Hcut (fun t _=>d.radius_cdf_limit t)
      (by dsimp only [R]; linarith) (fun delta hd _=>hp delta hd)
  have Hr n : Measurable (radius n) :=
    ((comparisonSweepQuantile_continuous (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).measurable.comp
        measurable_subtype_coe).div_const _
  have Hmi n : Integrable (fun w=>spin n w-radius n w) (mu n) := by
    have Hsm : Measurable (spin n) := by
      have Hmono : Monotone (fun w : ParisiFinite.OrderPoint=>
          orderedPathS (dim n+1) (M n).bf (M n).hf w) :=
        fun u v huv=>(M n).mass_mean_monotone u.property v.property huv
      exact Hmono.measurable.div_const _
    apply Integrable.of_bound ((Hsm.sub (Hr n)).aestronglyMeasurable) (1/(M n).xs)
    filter_upwards [] with w
    have HS := (M n).mass_mean_unit_bounds w.property
    have HR := comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha w
    dsimp only [spin,radius,Pi.sub_apply]
    rw [Real.norm_eq_abs,←sub_div,abs_div,abs_of_pos (M n).hxs]
    apply div_le_div_of_nonneg_right _ (M n).hxs.le
    exact abs_le.mpr ⟨by linarith only [HS.1,HR.2],by linarith only [HS.2,HR.1]⟩
  have Hfull := actual_selected_bad_history_initial_mass_absolute_mismatch_ratio_tendsto_zero_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
      (fun _=>le_rfl) hx G C hC
  have Hmis : Tendsto (fun n=>∫w,|spin n w-radius n w|∂mu n) atTop (𝓝 0) := by
    apply Hfull.congr'
    filter_upwards [Hsmall] with n hn
    rw [comparison_normalized_clock_error_exact
      (orderedPathS (dim n+1) (M n).bf (M n).hf) (M n).R (M n).hxs,
      comparison_original_retained_integral_eq_interval (hv n)
        (fun u=>|orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|)]
    simp only [v,min_eq_left hn]
  obtain ⟨ns,hns,w,Hrsel,Hssel,_⟩ := comparison_mass_support_exists_scalar_selections
    mu (fun _=>inferInstance) radius spin (fun _ _=>0) Hr
    (fun _=>by
      apply Integrable.of_bound (by simpa only [abs_zero] using aestronglyMeasurable_const) 0
      filter_upwards [] with w
      simp only [abs_zero,norm_zero,le_refl]) (fun n=>(Hmi n).abs)
    (by simpa only [abs_zero,integral_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0)))
    Hmis Hmass
  exact ⟨ns,hns,w,Hrsel,Hssel⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 12000000

theorem actual_selected_bad_history_radius_spin_between_support_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Slocal c0 : ℝ} (hT : 0 < T)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData hT Slocal M htotal)
    (s : NonnegativeMassProfile)
    (Hspin : ∀t : ℝ,Tendsto (fun n=>orderedPathS (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))/(M n).xs) atTop (𝓝 (s.mass t)))
    {a b t : ℝ} (hat : a < t) (htb : t < b)
    (hasupport : ∀eps : ℝ,0 < eps → d.V.mass (a-eps) < d.V.mass (a+eps))
    (hbsupport : ∀eps : ℝ,0 < eps → d.V.mass (b-eps) < d.V.mass (b+eps)) :
    s.mass t∈Icc a b := by
  obtain ⟨ns,hns,w,Hr,Hs⟩ := exists_actual_selected_bad_history_support_spin_selections_along_weak_general
    hT hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim
    G htotal d a hasupport
  have Hlower : a ≤ s.mass t := by
    apply le_of_tendsto_of_tendsto Hs ((Hspin t).comp hns)
    filter_upwards [Hr.eventually (gt_mem_nhds hat)] with j hj
    apply div_le_div_of_nonneg_right _ (M (ns j)).hxs.le
    apply (M (ns j)).mass_mean_le_radius_mean_of_radius_le (w j).property
    have H := (div_lt_iff₀ (M (ns j)).hxs).mp hj
    simpa only [mul_comm] using H.le
  obtain ⟨ms,hms,z,Hr',Hs'⟩ := exists_actual_selected_bad_history_support_spin_selections_along_weak_general
    hT hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim
    G htotal d b hbsupport
  have Hupper : s.mass t ≤ b := by
    apply le_of_tendsto_of_tendsto ((Hspin t).comp hms) Hs'
    filter_upwards [Hr'.eventually (lt_mem_nhds htb)] with j hj
    apply div_le_div_of_nonneg_right _ (M (ms j)).hxs.le
    apply (M (ms j)).radius_mean_le_mass_mean_of_le_radius (z j).property
    have H := (lt_div_iff₀ (M (ms j)).hxs).mp hj
    simpa only [mul_comm] using H.le
  exact ⟨Hlower,Hupper⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_radius_scalar_gap_integral_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        (∫r in (M n).actualRadiusTargetStrip c C,
          |orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)-
            scalarCovarianceResponse (G.hT)
              ((M n).inheritedScalarMassProfile
                (G.hT) htotal)
              (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))|)/
          (M n).xs^4 ≤ eta n := by
  have hTemp : 0 < T := G.hT
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have HW : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    convert hWlim using 1
    exact funext (fun n=>(hcanonical n).symm)
  have Hthermal := actual_selected_bad_history_radius_strip_thermal_tendsto_zero_along_weak_general
    (c:=c) (C:=C) Bclock hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc
    dim hdim M hx G
  obtain ⟨Cp,hCp,rate,hrate,Hrate,Hpoint⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_pointwise_along_weak_general C hC
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  let eta := fun n=>Cp*Real.sqrt (C*((∫r in (M n).actualRadiusTargetStrip c C,
      (M n).cavityRadiusPointDefect r)/(M n).xs^3))+
      Cp*C/((M n).context.N*(M n).xs)+C*rate n
  have Hsite:=actual_scalar_gap_site_ratio_tendsto_zero_along hm hC0 dim hdim M HW
  have Heta : Tendsto eta atTop (𝓝 0) := by
    have H:=(((Hthermal.const_mul C).sqrt.const_mul Cp).add (Hsite.const_mul (Cp*C))).add
      (Hrate.const_mul C)
    simpa only [eta,mul_zero,Real.sqrt_zero,add_zero,mul_one_div] using H
  refine ⟨eta,?_,Heta,?_⟩
  · intro n
    exact add_nonneg (add_nonneg (mul_nonneg hCp (Real.sqrt_nonneg _))
      (div_nonneg (mul_nonneg hCp hC.le)
        (mul_nonneg (M n).context.hN.le (M n).hxs.le)))
      (mul_nonneg hC.le (hrate n))
  · filter_upwards [Hpoint] with n hn
    obtain ⟨htotal,hn⟩:=hn
    refine ⟨htotal,?_⟩
    let F:=(M n).actualRadiusTargetStrip c C
    have := (M n).actual_radius_target_strip_finite_measure c C
    apply (M n).actual_original_radius_scalar_modulus_integral_le
      (G.hT) _ F
      ((M n).actual_radius_target_strip_measurable c C)
      (fun r hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
      hCp hC.le (hrate n)
    · simpa only [measureReal_restrict_apply_univ] using
        (M n).actual_radius_target_strip_measure_le c C hC.le
    · intro r hr
      exact hn ((M n).alpha.val.val r) ((mul_pos hc (M n).hxs).trans_le hr.2.1) hr.2.2

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_compact_radius_cavity_L1_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (_hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    Tendsto (fun n=>∫t in Icc a b,
      |(orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val ((M n).xs*t))-
        scalarCovarianceResponse (G.hT)
          ((M n).inheritedScalarMassProfile (G.hT) (htotal n))
          (actualMixedClock (dim n+1) (M n).bf (M n).hf
            ((M n).alpha.val.val ((M n).xs*t))))/(M n).xs^3|) atTop (𝓝 0) := by
  have hTemp : 0 < T := G.hT
  let Cbig:=max 1 (max C b)
  have hbig : 0 < Cbig:=zero_lt_one.trans_le (le_max_left _ _)
  have hCb : C ≤ Cbig := (le_max_left _ _).trans (le_max_right _ _)
  have hbb : b ≤ Cbig := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨eta,heta,Heta,Hbound⟩:=
    exists_actual_selected_bad_history_radius_scalar_gap_integral_along_weak_general c Cbig hc hbig
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hxb : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
    simpa only [zero_mul] using hx.mul_const b
  have hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 :=
    hxb.eventually (eventually_le_nhds zero_lt_one)
  apply squeeze_zero' (Eventually.of_forall (fun n=>integral_nonneg (fun t=>abs_nonneg _))) _ Heta
  filter_upwards [Hbound,hmass,hsmall] with n hn hmN hsN
  obtain ⟨ht,hn⟩:=hn
  let f:=fun r=>orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)-
    scalarCovarianceResponse (G.hT)
      ((M n).inheritedScalarMassProfile (G.hT) (htotal n))
      (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))
  have hf : IntegrableOn f ((M n).actualRadiusTargetStrip c Cbig) :=
    ((M n).original_scalar_radius_gap_integrableOn
      (G.hT) _).mono_set
      (fun r hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
  have H:=(M n).radius_scalar_residual_compact_integral_le ha hab.le hbb hsN
    (fun t ht=>⟨(hmN t ht).1,(hmN t ht).2.trans
      (mul_le_mul_of_nonneg_right hCb (M n).hxs.le)⟩) f hf
  exact H.trans hn

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 8000000

theorem actual_selected_bad_history_radius_clock_control_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (C a b : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))
    let q := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))/(T*(M n).xs)
    ∃Cs Q : ℝ,0 < Cs ∧ 0 < Q ∧
      (∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs ∧ q n t∈Icc (0:ℝ) Q) ∧
      TendstoUniformlyOn (fun n t=>
        (((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
          (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3)
        (fun _=>0) atTop (Icc a b) := by
  have hTemp : 0 < T := G.hT
  intro S q
  have Hnear := actual_selected_bad_shell_history_near_bare_clocks_weak_general
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G (fun n=>(M n).xs)
    (Eventually.of_forall (fun _=>le_rfl)) hxs
  have Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs),|(M n).h u| ≤ (M n).xs^3 := by
    filter_upwards [Hnear C 1 hC.le zero_lt_one] with n hn u hu
    simpa only [one_mul] using (hn u hu).2
  obtain ⟨Q,hQ,HQ⟩ := actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M hxs
    (G.hT) hTemp htotal C hC Hfield
  obtain ⟨B,hB,HB⟩ := eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs := B*(1+C)
  have hCs : 0 < Cs := by dsimp only [Cs];positivity
  have HS : ∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs := by
    filter_upwards [hdim.eventually HB,hmass] with n hn hmN t ht
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (0:ℝ) 1 := (M n).alpha.val.property.1 _
    refine ⟨(M n).mass_mean_nonneg hu,?_⟩
    by_cases hzero : u=0
    · change orderedPathS (dim n+1) (M n).bf (M n).hf u ≤ _
      simp only [hzero,orderedPathS,orderedPathPair_zero]
      exact mul_nonneg hCs.le (M n).hxs.le
    · have H := hn (M n) u ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero),hu.2⟩
      have Hmul := mul_le_mul_of_nonneg_left (hmN t ht) hB.le
      dsimp only [S,Cs,u] at *
      nlinarith only [H,Hmul]
  refine ⟨Cs,Q,hCs,hQ,?_,?_⟩
  · filter_upwards [HS,HQ,hmass] with n hn hqn hmN t ht
    exact ⟨(hn t ht).1,(hn t ht).2,hqn
      ⟨(M n).alpha.val.val ((M n).xs*t),(M n).alpha.val.property.1 _⟩ (hmN t ht)⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    let e := eps/(2*(Cs+1))
    have he : 0 < e := by dsimp only [e];positivity
    filter_upwards [HS,hmass,Hnear C e hC.le he] with n hn hmN hnear t ht
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (0:ℝ) (C*(M n).xs) := ⟨((M n).alpha.val.property.1 _).1,hmN t ht⟩
    obtain ⟨hbN,hhN⟩ := hnear u hu
    have Hmul := mul_le_mul hbN (hn t ht).2 (hn t ht).1
      (mul_nonneg he.le (sq_nonneg (M n).xs))
    have Habs := abs_add_le (((M n).b u-T)*S n t) ((M n).h u)
    rw [abs_mul,abs_of_nonneg (hn t ht).1] at Habs
    have Hbound : |(((M n).b u-T)*S n t+(M n).h u)/(M n).xs^3| ≤ (Cs+1)*e := by
      rw [abs_div,abs_of_pos (pow_pos (M n).hxs 3)]
      apply (div_le_iff₀ (pow_pos (M n).hxs 3)).mpr
      nlinarith only [Habs,Hmul,hhN]
    have Heq : (Cs+1)*e=eps/2 := by dsimp only [e];field_simp
    have Hlt := Hbound.trans_lt (show (Cs+1)*e < eps by rw [Heq];linarith)
    simpa only [Real.dist_eq,zero_sub,abs_neg,u] using Hlt

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 22000000

theorem actual_selected_bad_history_bounded_radius_scalar_closure_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (d : ActualInheritedLocalScalarLimitData (G.hT)
      T M htotal)
    (L A : ℝ) (s : NonnegativeMassProfile)
    (Hstrength : ∀t∈Icc a b,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hspin : ∀t∈Icc a b,Tendsto (fun n=>
      orderedPathS (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t))/(M n).xs) atTop (𝓝 (s.mass t))) :
    let g := comparisonLocalScalarLimitResponse (G.hT)
      T d.beta d.U d.sigma
    ∀ᵐ t∂volume.restrict (Icc a b),
      g (s.mass t)=(L*laplaceComparisonShape (A*t))/T*(s.mass t-t) := by
  have hTemp : 0 < T := G.hT
  intro g
  let hT : 0 < T := G.hT
  let Gamma := fun n=>scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n))
  let u := fun n t=>(M n).alpha.val.val ((M n).xs*t)
  let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf (u n t)
  let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf (u n t)
  let e := fun n t=>laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)
  let b0 := fun n t=>(M n).b (u n t)
  let h0 := fun n t=>(M n).h (u n t)
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have HrhoL1 : Tendsto (fun n=>∫t in Icc a b,
      |(S n t-Gamma n (K n t))/(M n).xs^3|) atTop (𝓝 0) :=
    actual_selected_bad_history_compact_radius_cavity_L1_along_weak_general c C a b hc hC ha hab
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare htotal hmass
  have Hrhoi : ∀n,Integrable (fun t=>(S n t-Gamma n (K n t))/(M n).xs^3)
      (volume.restrict (Icc a b)) := fun n=>(M n).rescaled_radius_scalar_gap_integrableOn
        hT ((M n).inheritedScalarMassProfile hT (htotal n)) a b
  obtain ⟨phi,hphi,Hrho⟩ := comparison_L1_zero_exists_ae_subsequence
    (volume.restrict (Icc a b)) (fun n t=>(S n t-Gamma n (K n t))/(M n).xs^3) Hrhoi HrhoL1
  obtain ⟨Cs,Q,hCs,hQ,Hclock,Hz⟩ := actual_selected_bad_history_radius_clock_control_along_weak_general
    C a b hC hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G hx htotal
    (hmass.mono (fun _ hn t ht=>(hn t ht).2))
  let Qbig := max Q Cs
  have hQbig : 0 < Qbig := hQ.trans_le (le_max_left _ _)
  have Hrange : ∀ᶠn in atTop,∀t∈Icc a b,K n t/(T*(M n).xs)∈Icc (0:ℝ) Qbig := by
    filter_upwards [Hclock] with n hn t ht
    exact ⟨(hn t ht).2.2.1,(hn t ht).2.2.2.trans (le_max_left _ _)⟩
  have Hsrange : ∀t∈Icc a b,s.mass t∈Icc (0:ℝ) Qbig := by
    intro t ht
    refine ⟨s.nonneg t,?_⟩
    apply le_trans _ (le_max_right _ _)
    apply le_of_tendsto (Hspin t ht)
    filter_upwards [Hclock] with n hn
    exact (div_le_iff₀ (M n).hxs).mpr (by simpa only [mul_comm] using (hn t ht).2.1)
  have Hgc : ContinuousOn g (Icc (0:ℝ) Qbig) := by
    have Hi : IntegrableOn (comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma)
        (Icc (0:ℝ) Qbig) := (d.limits Qbig hQbig).1.integrableOn_Icc
    change ContinuousOn (fun q=>∫r in 0..q,
      comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma r) (Icc (0:ℝ) Qbig)
    have Hi' : IntegrableOn (comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma)
        (uIcc (0:ℝ) Qbig) := by simpa only [uIcc_of_le hQbig.le] using Hi
    simpa only [uIcc_of_le hQbig.le] using intervalIntegral.continuousOn_primitive_interval Hi'
  have Hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hnative : ∀ᶠn in atTop,∀t∈Icc a b,K n t=
      comparisonNativeScalarClock (h0 n t) (b0 n t) (e n t) ((M n).xs*t) (S n t) := by
    filter_upwards [Hsmall] with n hn t ht
    exact (M n).radius_mixed_clock_eq_nativeScalarClock
      ⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),
        (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hn⟩
  filter_upwards [Hrho,ae_restrict_mem measurableSet_Icc] with t hrhot ht
  apply comparison_scalar_closure_identification_combined_bare
    (fun n=>Gamma (phi n)) (fun n=>h0 (phi n) t) (fun n=>b0 (phi n) t)
    (fun n=>e (phi n) t) (fun n=>S (phi n) t) (fun n=>(M (phi n)).xs) g
    hTemp.ne' (fun n=>(M (phi n)).hxs.ne') (hx.comp hphi.tendsto_atTop)
    ((Hstrength t ht).comp hphi.tendsto_atTop) ((Hspin t ht).comp hphi.tendsto_atTop)
    ((Hz.tendsto_at ht).comp hphi.tendsto_atTop)
    ((d.limits Qbig hQbig).2.2.seq_tendstoUniformlyOn phi hphi.tendsto_atTop)
    (Hgc _ (Hsrange t ht))
  · filter_upwards [hphi.tendsto_atTop.eventually Hnative,hphi.tendsto_atTop.eventually Hrange]
      with n hn hr
    rw [←hn t ht]
    exact hr t ht
  · apply hrhot.congr'
    filter_upwards [hphi.tendsto_atTop.eventually Hnative] with n hn
    rw [←hn t ht]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 22000000

theorem actual_selected_bad_history_bounded_gap_scalar_closure_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData (G.hT)
      T M htotal)
    (L A : ℝ) (s : NonnegativeMassProfile)
    (Hstrength : ∀t : ℝ,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hspin : ∀t : ℝ,Tendsto (fun n=>
      orderedPathS (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t))/(M n).xs) atTop (𝓝 (s.mass t)))
    (hasupport : a∈comparisonIncrementSupport d.V.mass)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) :
    let g := comparisonLocalScalarLimitResponse (G.hT)
      T d.beta d.U d.sigma
    ∀ᵐt∂volume.restrict (Ioo a b),
      g (s.mass t)=(L*laplaceComparisonShape (A*t))/T*(s.mass t-t) := by
  have hTemp : 0 < T := G.hT
  intro g
  have hmass : 0 < d.V.mass ((a+b)/2) :=
    comparison_increment_support_positive_cdf_after d.V.monotone d.radius_negative_axis_zero
      hasupport (by linarith)
  let c := d.V.mass ((a+b)/2)/2
  let C := d.V.mass ((a+b)/2)+1
  have hc : 0 < c := half_pos hmass
  have hC : 0 < C := by dsimp only [C]; linarith
  apply comparison_ae_on_open_interval_of_compact_interiors
  intro left hleft right hright hlr
  have Hmass := actual_compact_gap_mass_band_along dim M d.V.mass d.V.monotone
    d.radius_inverse_cdf_limit hab hgap hmass hleft hright
  exact actual_selected_bad_history_bounded_radius_scalar_closure_along_weak_general
    c C left right hc hC (ha.trans hleft.1.le) hlr
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim
    hcompare htotal Hmass d L A s (fun t _=>Hstrength t) (fun t _=>Hspin t)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 22000000

theorem actual_selected_bad_history_bounded_virtual_gap_data_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData (G.hT)
      T M htotal)
    (L A : ℝ) (s : NonnegativeMassProfile) (hL : 0 < L) (hA : 0 ≤ A)
    (Hstrength : ∀t,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
      atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hslope : ∀t,Tendsto (fun n=>comparisonLogSlope
      (laplaceComparisonStrength (M n).context.d (M n).lam) ((M n).xs*t))
      atTop (𝓝 (laplaceComparisonSlope (A*t))))
    (Hspin : ∀t,Tendsto (fun n=>(M n).actualScaledRadiusSpin t) atTop (𝓝 (s.mass t)))
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport d.V.mass)
    (hbsupport : b∈comparisonIncrementSupport d.V.mass)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) :
    Nonempty (ComparisonVirtualGapData
      (comparisonLocalScalarLimitResponse (G.hT)
        T d.beta d.U d.sigma) a b) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨Kj,hKj,j,hj,Hj,⟨P⟩⟩ :=
    actual_selected_bad_history_bounded_virtual_gap_primitive_along_weak_general K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hwork htotal d L A s hL hA Hstrength Hslope Hspin ha hab hbB
      hasupport hbsupport hgap
  apply Nonempty.intro
  apply comparison_bounded_pinned_primitive_to_gap ha hL hTemp P
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact lt_of_lt_of_le (by positivity : 0 < 1/Kj^2) (Hj t ⟨ht.1.le,ht.2.le⟩).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact actual_selected_bad_history_radius_spin_between_support_along_weak_general
      (G.hT) hm hdelta hroom hcl hcu hAz hC0 hCt
      dim hdim M W hcanonical hWlim G htotal d s
      Hspin ht.1 ht.2 hasupport hbsupport
  · exact actual_selected_bad_history_bounded_gap_scalar_closure_along_weak_general ha hab
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare htotal d L A s Hstrength Hspin hasupport hgap

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_joint_scalar_limit_with_virtual_gaps_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal,
          ∀a b : ℝ,0 ≤ a → a < b →
            a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
            (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
            Nonempty (ComparisonVirtualGapData
              (comparisonLocalScalarLimitResponse (G.hT)
                T d.beta d.U d.sigma) a b) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,⟨d⟩,L,A,B,s,hL,hA,hB,HL,HA,Hpositive,Hbound,Hs,Hgradient⟩ :=
    exists_actual_selected_bad_history_bounded_radius_gradient_limit_along_weak_general K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hwork
  refine ⟨phi,hphi,htotal,d,?_⟩
  intro a b ha hab hasupport hbsupport hgap
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 1/Ccal^2) hL.1
  exact actual_selected_bad_history_bounded_virtual_gap_data_along_weak_general (B:=b+1)
    K hK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n))
    (hphi.tendsto_atTop.eventually hwork) htotal d L A s hLpos hA.1 HL HA Hs
    ha hab (by linarith) hasupport hbsupport hgap

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy GaussianCalculus Scalar
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

namespace ActualInheritedLocalScalarLimitData

theorem scalar_radius_laws_ae_eq_of_actual_history_weak_general
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u  ≤  T}
    (d : ActualInheritedLocalScalarLimitData hT T M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0) :
    d.U.mass=ᵐ[volume] d.V.mass := by
  have hlocal : 0 < T := G.hT
  let gamma:=T/T
  let x:=fun n=>(M n).xs
  let q:=fun n=>actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf
  have hgamma:0 < gamma:=div_pos hlocal hT
  have hx:∀n,0 < x n:=fun n=>(M n).hxs
  have hxlim:Tendsto x atTop (𝓝 0):=
    squeeze_zero (fun n=>(M n).hxs.le)
      (fun n=>(M n).canonical_direct_test_band_ge_scale) hcanonical
  have hq:∀n,MonotoneOn (q n) (Icc (0:ℝ) 1):=fun n=>
    actualScalarClockQuantile_monotone hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
  have hqb:∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1:=fun n=>
    actualScalarClockQuantile_bounds hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
      ((M n).inherited_total_clock_le (htotal n))
  have hU:∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val
      (gamma*(x n*t))/x n) atTop (𝓝 (d.U.mass t)):=d.scalar_cdf_limit
  have hlocalLaw:∀R : ℝ,0 < R → ∃v : ℕ → ℝ,
      (∀n,v n∈Icc (0:ℝ) 1) ∧
      (∀ᶠn in atTop,gamma*(x n*R) < q n (v n) ∧ x n*R < (M n).R (v n)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
        |q n (w:ℝ)/gamma-(M n).R w|∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0) := by
    intro R hR
    obtain ⟨C,hC,Hcut,Hcouple⟩:=
      actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along_weak_general
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M x (fun _=>le_rfl) hxlim G R hR
    let v:=fun n=>min (C*x n) 1
    have hv:∀n,v n∈Icc (0:ℝ) 1:=fun n=>
      ⟨le_min (mul_nonneg hC.le (hx n).le) zero_le_one,min_le_right _ _⟩
    refine ⟨v,hv,?_,?_⟩
    · filter_upwards [Hcut] with n hn
      refine ⟨?_,hn.2⟩
      have hv0:0 < v n:=lt_min (mul_pos hC (hx n)) zero_lt_one
      have H:=mul_lt_mul_of_pos_left hn.1 hgamma
      dsimp only [q]
      rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf hv0]
      convert H using 1; dsimp only [gamma,v];field_simp [hT.ne',hlocal.ne']
    · have Hroot:=actual_selected_bad_history_total_clock_and_root_weak_general
        dim M G
      apply Hcouple.congr'
      filter_upwards [Hroot] with n hn
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun w=>by
        dsimp only [q,gamma]
        rw [actual_ambient_scalar_quantile_div_local_ratio (M n) hT hlocal,
          (M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root T hn.2 w.property.1]
  exact comparison_shifted_local_temperature_scalar_radius_laws_ae_identified
    (actualInverseSequence M) q gamma x d.U.mass d.V.mass hgamma
    (fun _=>le_rfl) hq hqb hx d.V.monotone
    (actualInverseSequence_omitted_small M x) hU d.radius_inverse_cdf_limit hlocalLaw

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 8000000

namespace ActualInheritedLocalScalarLimitData

theorem global_profile_rigidity_of_actual_history_weak_general
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualInheritedLocalScalarLimitData hT T M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    
    (hcanonical : Tendsto (fun n => (M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (G : ActualNativeProfileHistory M T c0)
    (hvirtual : ∀a b,0 ≤ a → a < b →
      a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma) a b)) :
    (∀t > 0,d.U.mass t=((T/T)*scalarInitialDensityConstant hT d.beta)*t) ∧
    (∀t > 0,d.V.mass t=((T/T)*scalarInitialDensityConstant hT d.beta)*t) := by
  have hlocal : 0 < T := G.hT
  have hUV := d.scalar_radius_laws_ae_eq_of_actual_history_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin hdim
    hcanonical G
  have hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n => (M n).hxs.le)
      (fun n => (M n).canonical_direct_test_band_ge_scale) hcanonical
  exact d.global_profile_rigidity_of_coupled_laws hUV hcl hAz hxs hvirtual

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_linear_profile_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal,
          let kappa := (T/T)*scalarInitialDensityConstant
            (G.hT) d.beta
          (∀t>0,d.U.mass t=kappa*t) ∧ (∀t>0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,d,Hvirtual⟩ :=
    exists_actual_selected_bad_history_bounded_joint_scalar_limit_with_virtual_gaps_along_weak_general K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hwork
  have Hcan : Tendsto (fun n=>(M (phi n)).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    have H := hWlim.comp hphi.tendsto_atTop
    simpa only [Function.comp_def,hcanonical] using H
  have Hlinear := d.global_profile_rigidity_of_actual_history_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    (hdim.comp hphi.tendsto_atTop) Hcan (G.comp phi hphi) Hvirtual
  refine ⟨phi,hphi,htotal,d,Hlinear.1,Hlinear.2,?_⟩
  have hx : Tendsto (fun n=>(M (phi n)).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(M (phi n)).hxs.le)
      (fun n=>(M (phi n)).canonical_direct_test_band_ge_scale) Hcan
  let t := max Az 1
  have ht : 0 < t := zero_lt_one.trans_le (le_max_right _ _)
  have Hgrowth := d.radius_outer_growth hAz hx t (le_max_left _ _)
  rw [Hlinear.2 t ht] at Hgrowth
  exact ⟨le_of_mul_le_mul_right Hgrowth.1 ht,le_of_mul_le_mul_right Hgrowth.2 ht⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_high_strength_scalar_calibration_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
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
          |scalarCovarianceResponse (G.hT)
            ((M n).inheritedScalarMassProfile (G.hT) htotal)
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
  obtain ⟨ps,Hps⟩ := G.literal_readout
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
    filter_upwards [Hps] with n hn
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha T (G.epsilon n) (G.shell n) ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
      (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl
  obtain ⟨Cs,hCs,Hband⟩ := eventually_actual_regular_calibrated_mass_band
    hm hdelta hroom hcl hcu hAz hC0 hCt (L:=1) (by norm_num)
    dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl) hxlim Hclock
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_weak_general
      b hbpos hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have Hnear := actual_selected_bad_shell_history_near_bare_clocks_weak_general
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G (fun n=>(M n).xs)
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
    (G.hT) htotal
  have hfi : IntervalIntegrable f volume 0 (b*(M n).xs) :=
    (M n).original_scalar_gap_intervalIntegrable
      (G.hT)
      ((M n).inheritedScalarMassProfile (G.hT) htotal)
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
      T*orderedPathS (dim n+1) (M n).bf (M n).hf u| ≤ Ck*(M n).xs^3 := by
    let S := orderedPathS (dim n+1) (M n).bf (M n).hf u
    let e := laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)
    have hid : comparisonNativeScalarClock ((M n).h u) ((M n).b u) e ((M n).R u) S-
        T*S = (M n).h u+((M n).b u-T)*S+e*((M n).R u-S) := by
      unfold comparisonNativeScalarClock
      ring
    rw [(M n).inherited_mixed_clock_eq_nativeScalarClock hu01]
    change |comparisonNativeScalarClock ((M n).h u) ((M n).b u) e ((M n).R u) S-
      T*S| ≤ _
    rw [hid]
    have HE : |e*((M n).R u-S)| ≤ (M n).xs^3 := by
      rw [show e*((M n).R u-S)=-(e*(S-(M n).R u)) by ring,abs_neg]
      exact Hweighted
    have HB := mul_le_mul Hnear.1 hShi hSu
      (show (0:ℝ) ≤ 1*(M n).xs^2 by positivity)
    have H := (abs_add_le ((M n).h u+((M n).b u-T)*S)
      (e*((M n).R u-S))).trans
      (add_le_add (abs_add_le ((M n).h u) (((M n).b u-T)*S)) le_rfl)
    rw [abs_mul,abs_of_nonneg hSu] at H
    dsimp only [Ck]
    nlinarith only [H,HE,HB,Hnear.2]
  refine ⟨htotal,actualMixedClock (dim n+1) (M n).bf (M n).hf u/T,?_⟩
  exact scalar_calibration_at_local_temperature
    (scalarCovarianceResponse (G.hT)
      ((M n).inheritedScalarMassProfile (G.hT) htotal))
    hTemp (M n).hxs hnUnit hCk hSlo hShi hclock hnSmall
    (show |orderedPathS (dim n+1) (M n).bf (M n).hf u-
      scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) htotal)
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤ 1*(M n).xs^3 by
      simpa only [one_mul,f,inheritedScalarCavityResidual] using hres)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_scalar_compactness_of_total_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
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
  have hx : Tendsto x atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hcaps := actual_selected_bad_history_local_temperature_original_scalar_cdf_caps_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M x (fun _=>le_rfl) hx G
  have hcap : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧
      ∀ᶠn in atTop,(alpha n).val ((T/T)*(x n*R))≤A*x n := by
    intro R hR
    obtain ⟨A,hA,HA⟩ := Hcaps.2 R hR
    exact ⟨A,hA.le,HA.mono fun n hn=>hn (htotal n)⟩
  have hradiusCap : ∀R : ℝ,0<R→∃A : ℝ,
      ∀ᶠn in atTop,(radiusCDF n).val (x n*R)/x n≤A := by
    intro R hR
    obtain ⟨A,hA,HA,_⟩ :=
      actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along_weak_general
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M x (fun _=>le_rfl) hx G R hR
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
    exists_actual_selected_bad_history_high_strength_scalar_calibration_along_weak_general
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
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

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_high_strength_response_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
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
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let hT:=G.hT
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let G:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n)))
        T (M n).xs
    let q:=fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/(T*(M n).xs)
    (∀n,Integrable (fun z=>G n (q n z)) (nu n)) ∧
      Tendsto (fun n=>∫z,|G n (q n z)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun z=>q n z-(M n).R z/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫z,|q n z-(M n).R z/(M n).xs|∂nu n) atTop (𝓝 0) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨_eta,_heta,_hetalim,_Henvelope,Hcavity⟩:=
    exists_actual_selected_bad_history_normalized_scalar_gap_along_weak_general
      C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have Hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity_weak_general
    dim M G
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks_weak_general
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G (fun n=>(M n).xs)
    (Eventually.of_forall fun _=>le_rfl) Hxs
  have Hbare : ∀eps > 0,∀ᶠn in atTop,∀z : ParisiFinite.OrderPoint,z.val ≤ v n →
      |(M n).b z-T| ≤ eps*(M n).xs^2 ∧
        |(M n).h z| ≤ eps*(M n).xs^3 := by
    intro eps heps
    filter_upwards [Hnear C eps hC.le heps] with n hn
    intro z hz
    exact hn z ⟨z.property.1,hz.trans (hvc n)⟩
  have Hcav:=Hcavity htotal v hv (Eventually.of_forall hvc)
  have HbareRate:=actual_inherited_restricted_bare_error_of_vanishing_clocks_along
    (T:=T) hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
    (fun _=>le_rfl) (fun n=>{z : ParisiFinite.OrderPoint | (z:ℝ) ≤ v n})
    (fun _=>measurableSet_le measurable_subtype_coe measurable_const) C hC
    (fun n z hz=>hz.trans (hvc n)) Hbare
  have Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs), |(M n).h u| ≤ (M n).xs^3 := by
    filter_upwards [Hnear C 1 hC.le (by norm_num)] with n hn u hu
    simpa only [one_mul] using (hn u hu).2
  obtain ⟨Rclock,hRclock,Hrange⟩:=actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M Hxs
    (G.hT) hTemp htotal C hC Hfield
  have HrangeV : ∀ᶠn in atTop,∀z : ParisiFinite.OrderPoint,(z:ℝ) ≤ v n →
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/(T*(M n).xs)∈Icc (0:ℝ) Rclock := by
    filter_upwards [Hrange] with n hn z hz
    exact hn z (hz.trans (hvc n))
  have Hweighted:=actual_high_strength_full_weighted_mass_tendsto_zero_along
    hdelta hcl hAz hC0 (by linarith only [hm,hdelta]) dim hdim M hlarge C hC.le v hv hvc
    (G.hT) hTemp htotal Hcav.2 HbareRate.2
    Rclock HrangeV g (hG Rclock hRclock) (hg Rclock hRclock)
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {z | (z:ℝ) ≤ v n}
  let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let S:=fun n (z : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf z
  let rad:=fun n (z : ParisiFinite.OrderPoint)=>(M n).R z
  let e:=fun n z=>laplaceComparisonStrength (M n).context.d (M n).lam (rad n z)
  let Gamma:=fun n=>scalarCovarianceResponse (G.hT)
    ((M n).inheritedScalarMassProfile (G.hT) (htotal n))
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

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem actual_selected_bad_history_high_strength_support_zero_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
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
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
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
  have Hresponse:=actual_selected_bad_history_high_strength_response_along_weak_general
    C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare hlarge htotal v hv hvc g hG hg
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

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_of_total_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
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
    exists_actual_selected_bad_history_high_scalar_compactness_of_total_along_weak_general
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
  exact actual_selected_bad_history_high_strength_support_zero_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n))
    (hlarge.comp hphi.tendsto_atTop) (fun n=>htotal (phi n))
    V.mass g ht hRt (fun a _=>hV a) (fun e he _=>hsupport e he) (fun R hR=>(Hphysical R hR).2.2) Hcontinuous

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
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
  obtain ⟨psi,hpsi,Hlimit⟩:=exists_actual_selected_bad_history_high_joint_scalar_limit_of_total_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    (fun n=>dim (shift n)) (hdim.comp hshift.tendsto_atTop) (fun n=>M (shift n))
    (G.comp shift hshift) (fun n=>W (shift n)) (fun n=>hcanonical (shift n))
    (hWlim.comp hshift.tendsto_atTop) (fun n=>hcompare (shift n)) (hlarge.comp hshift.tendsto_atTop) ht0
  exact ⟨shift ∘ psi,hshift.comp hpsi,fun n=>ht0 (psi n),Hlimit⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_radius_scalar_gap_uniform_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃B : ℝ,0 < B ∧ ∀ᶠn in atTop,
      ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
      ∀r∈(M n).actualRadiusTargetStrip c C,
        |(orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)-
          scalarCovarianceResponse (G.hT)
            ((M n).inheritedScalarMassProfile
              (G.hT) htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)))/(M n).xs^3| ≤ B := by
  have hTemp : 0 < T := G.hT
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have HW : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    convert hWlim using 1
    exact funext (fun n=>(hcanonical n).symm)
  obtain ⟨Cp,hCp,rate,hrate,Hrate,Hpoint⟩:=
    exists_actual_selected_bad_history_original_scalar_gap_pointwise_along_weak_general C hC
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim hcompare
  obtain ⟨Cd,hCd,HD⟩:=eventually_actual_original_thermal_norm_upper_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M C hC.le
  have Hsite:=actual_scalar_gap_site_ratio_tendsto_zero_along hm hC0 dim hdim M HW
  let B:=Cp*(Cd+1)+1
  have hB : 0 < B:=by dsimp only [B];positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [Hpoint,HD,Hrate.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    Hsite.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn hDn hrate1 hsite1
  obtain ⟨htotal,hn⟩:=hn
  refine ⟨htotal,?_⟩
  intro r hr
  let u:=(M n).alpha.val.val r
  have hu : 0 < u:=(mul_pos hc (M n).hxs).trans_le hr.2.1
  have hu1 : u ≤ 1:=((M n).alpha.val.property.1 r).2
  have huC : u ≤ C*(M n).xs:=hr.2.2
  have HP:=hn u hu huC
  have HDD:=hDn u ⟨hu,hu1⟩ huC
  have HN : 1/(dim n+1:ℕ) ≤ (M n).xs:=by
    have H:=(div_le_iff₀ (mul_pos (M n).context.hN (M n).hxs)).mp hsite1
    apply (div_le_iff₀ (show (0:ℝ)<(dim n+1:ℕ) from by exact_mod_cast Nat.zero_lt_succ _)).mpr
    simpa only [NativeOverlapContext.N,mul_comm,mul_one] using H
  rw [abs_div,abs_of_pos (pow_pos (M n).hxs 3)]
  apply (div_le_iff₀ (pow_pos (M n).hxs 3)).mpr
  have HM:=mul_le_mul_of_nonneg_left (add_le_add HDD HN) (mul_nonneg hCp (sq_nonneg (M n).xs))
  have HE:=mul_le_mul_of_nonneg_right hrate1 (pow_pos (M n).hxs 3).le
  apply HP.trans
  dsimp only [B]
  nlinarith only [HM,HE]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_radius_uniform_identification_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    let Gamma := fun n=>scalarCovarianceResponse (G.hT)
      ((M n).inheritedScalarMassProfile (G.hT) (htotal n))
    let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))
    let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))
    TendstoUniformlyOn (fun n t=>S n t/(M n).xs) (fun t=>t) atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>K n t/(T*(M n).xs)) (fun t=>t) atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
      (K n t/(T*(M n).xs))) g atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>
      (((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
        (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3)
      (fun _=>0) atTop (Icc a b) := by
  have hTemp : 0 < T := G.hT
  intro Gamma S K
  let h0 := fun n t=>(M n).h ((M n).alpha.val.val ((M n).xs*t))
  let b0 := fun n t=>(M n).b ((M n).alpha.val.val ((M n).xs*t))
  let Hctx := G
  let Gresponse := fun n=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
  have hbpos : 0 < b := ha.trans_lt hab
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cs,Q,hCs,hQ,Hclock,Hz⟩ := actual_selected_bad_history_radius_clock_control_along_weak_general
    C a b hC hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M Hctx hx htotal
    (hmass.mono (fun _ hn _ ht=>(hn _ ht).2))
  let Qbig := max Q b
  have hQbig : 0 < Qbig := hQ.trans_le (le_max_left _ _)
  have Hrange : ∀ᶠn in atTop,∀t∈Icc a b,K n t/(T*(M n).xs)∈Icc (0:ℝ) Qbig := by
    filter_upwards [Hclock] with n hn t ht
    exact ⟨(hn t ht).2.2.1,(hn t ht).2.2.2.trans (le_max_left _ _)⟩
  obtain ⟨CG,hCG,Hscalar⟩ := comparison_scalar_compact_response_eventually_bounded
    Gresponse g (hG Qbig hQbig) (hg Qbig hQbig)
  let Cbig := max 1 (max C b)
  have hbig : 0 < Cbig := zero_lt_one.trans_le (le_max_left _ _)
  have hCb : C ≤ Cbig := (le_max_left _ _).trans (le_max_right _ _)
  have hbb : b ≤ Cbig := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨CR,hCR,Hrho⟩ := exists_actual_selected_bad_history_radius_scalar_gap_uniform_along_weak_general
    c Cbig hc hbig hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M Hctx W hcanonical hWlim hcompare
  have Hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hr : ∀ᶠn in atTop,∀t∈Icc a b,|(S n t-Gamma n (K n t))/(M n).xs^3| ≤ CR := by
    filter_upwards [Hrho,Hsmall,hmass] with n hn hs hmN t ht
    obtain ⟨htotalN,hn⟩ := hn
    apply hn ((M n).xs*t)
    refine ⟨⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),le_min ?_ ?_⟩,(hmN t ht).1,?_⟩
    · nlinarith only [ht.2,hbb,(M n).hxs]
    · exact (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs
    · exact (hmN t ht).2.trans (mul_le_mul_of_nonneg_right hCb (M n).hxs.le)
  have Hflat := comparison_strength_eventually_flat_of_divergence
    (fun n=>(M n).context.d) (fun n=>(M n).lam) (fun n=>(M n).xs)
    (Eventually.of_forall (fun n=>⟨(M n).context.hd,(M n).hlam,(M n).hxs,(M n).hld⟩)) hlarge hbpos
  have Hnative : ∀ᶠn in atTop,∀t∈Icc a b,K n t=
      comparisonNativeScalarClock (h0 n t) (b0 n t) (M n).lam ((M n).xs*t) (S n t) := by
    filter_upwards [Hsmall,Hflat] with n hs hf t ht
    have hrad : (M n).xs*t∈Icc (0:ℝ) 1 :=
      ⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),(mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs⟩
    have hinv := comparisonSweepQuantile_inverse (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha hrad
    change (M n).R ((M n).alpha.val.val ((M n).xs*t))=(M n).xs*t at hinv
    have H := (M n).inherited_mixed_clock_eq_nativeScalarClock ((M n).alpha.val.property.1 ((M n).xs*t))
    rw [hinv,(hf t ⟨ha.trans ht.1,ht.2⟩).1] at H
    exact H
  let Cprod := |T| *(CG+CR)+1
  have hprod : 0 ≤ Cprod := by dsimp only [Cprod];positivity
  have Hbudget : ∀ᶠn in atTop,∀t∈Icc a b,
      |((M n).lam/(M n).xs^2)*(S n t/(M n).xs-t)| ≤ Cprod := by
    filter_upwards [Hnative,Hrange,Hscalar,Hr,(Metric.tendstoUniformlyOn_iff.mp Hz) 1 zero_lt_one]
      with n hn hmN hGbound hr hz t ht
    apply comparison_scalar_product_bound (Gamma n) hTemp.ne' (M n).hxs.ne'
    · rw [←hn t ht]
      exact hGbound _ (hmN t ht)
    · rw [←hn t ht]
      exact hr t ht
    · simpa only [Real.dist_eq,zero_sub,abs_neg] using (hz t ht).le
  have Hlarge : Tendsto (fun n=>(M n).lam/(M n).xs^2) atTop atTop :=
    tendsto_atTop_mono (fun n=>div_le_div_of_nonneg_right
      (laplaceComparisonStrength_le (M n).context.d (M n).hlam.le (M n).xs)
      (sq_nonneg (M n).xs)) hlarge
  obtain ⟨Hspin,HqNative⟩ := comparison_large_strength_uniform_spin_clock h0 b0 S
    (fun n=>(M n).lam) (fun n=>(M n).xs) hTemp (fun n=>(M n).hxs) hx hprod Hlarge Hbudget Hz
  have Hq : TendstoUniformlyOn (fun n t=>K n t/(T*(M n).xs)) (fun t=>t) atTop (Icc a b) :=
    HqNative.congr (Hnative.mono (fun n hn t ht=>
      congrArg (fun z=>z/(T*(M n).xs)) (hn t ht).symm))
  have HP := comparison_uniform_response_at_moving_clock Gresponse g
    (fun n t=>K n t/(T*(M n).xs))
    (fun t ht=>⟨ha.trans ht.1,ht.2.trans (le_max_right _ _)⟩)
    (hG Qbig hQbig) (hg Qbig hQbig) Hq Hrange
  exact ⟨Hspin,Hq,HP,Hz⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_radius_gradient_L1_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    (∀ᶠn in atTop,IntegrableOn (M n).actualVirtualScaledGradient (Icc a b)) ∧
    Tendsto (fun n=>∫t in Icc a b,
      |(M n).actualVirtualScaledGradient t-(-2*T*g t)|) atTop (𝓝 0) := by
  have hTemp : 0 < T := G.hT
  let Gamma := fun n=>scalarCovarianceResponse (G.hT)
    ((M n).inheritedScalarMassProfile (G.hT) (htotal n))
  let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  let P := fun n t=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
    (K n t/(T*(M n).xs))
  let rho := fun n t=>(S n t-Gamma n (K n t))/(M n).xs^3
  let zeta := fun n t=>
    (((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
      (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3
  obtain ⟨_Hspin,_Hclock,HP,Hz⟩ := actual_selected_bad_history_high_radius_uniform_identification_along_weak_general
    c C a b hc hC ha hab hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare htotal hmass hlarge g hG hg
  have Hr := actual_selected_bad_history_compact_radius_cavity_L1_along_weak_general
    c C a b hc hC ha hab hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare htotal hmass
  have Hi n := (M n).actual_scaled_radius_scalar_integrability
    (G.hT) hTemp
    ((M n).inheritedScalarMassProfile (G.hT) (htotal n)) a b
  have hPi n : IntegrableOn (P n) (Icc a b) := (Hi n).2.2.2.1
  have hri n : IntegrableOn (rho n) (Icc a b) := (Hi n).2.2.1
  have hzi n : IntegrableOn (zeta n) (Icc a b) := (Hi n).2.2.2.2
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure
    dim M hx hlarge a b ha hab Gamma T hTemp
  have Heq : ∀ᶠn in atTop,∀t∈Icc a b,(M n).actualVirtualScaledGradient t=
      -2*T*(P n t+rho n t)-2*zeta n t := by
    filter_upwards [Hclosure] with n hn t ht
    simpa only [P,rho,zeta,S,K,mul_div_assoc] using (hn t ht).2
  have Hfi : ∀ᶠn in atTop,IntegrableOn (M n).actualVirtualScaledGradient (Icc a b) := by
    filter_upwards [Heq] with n hn
    apply (((hPi n).add (hri n)).const_mul (-2*T)).sub ((hzi n).const_mul 2) |>.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hn t ht).symm
  refine ⟨Hfi,?_⟩
  have hgi : IntegrableOn g (Icc a b) :=
    ((hg b (ha.trans_lt hab)).mono (fun t ht=>⟨ha.trans ht.1,ht.2⟩)).integrableOn_Icc
  exact comparison_scalar_density_eventual_L1_tendsto (fun n=>(M n).actualVirtualScaledGradient)
    P rho zeta g T a b Hfi hPi hri hzi hgi Heq HP Hr Hz

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem eventually_actual_history_high_gradient_uniform_above_mass_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c B : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    ∃CG : ℝ,0 < CG ∧ ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) →
        |(M n).actualVirtualScaledGradient t| ≤ CG := by
  have hTemp : 0 < T := G.hT
  let Gamma := fun n=>scalarCovarianceResponse (G.hT)
    ((M n).inheritedScalarMassProfile (G.hT) (htotal n))
  let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  let Cm := 1+cu*(B+Az)
  have hCm : 0 < Cm := by dsimp only [Cm];positivity
  have Hsmall : ∀ᶠn in atTop,(M n).xs*B ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*B) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const B
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hupper : ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      (M n).alpha.val.val ((M n).xs*t) ≤ Cm*(M n).xs := by
    filter_upwards [Hsmall] with n hn t ht
    let z := max ((M n).xs*B) (M n).z
    have hz : z∈Icc (M n).z 1 := ⟨le_max_right _ _,max_le hn (M n).hz.2⟩
    have hzsize : z ≤ (B+Az)*(M n).xs := by
      apply max_le
      · nlinarith only [mul_nonneg hAz (M n).hxs.le]
      · nlinarith only [(M n).hzxs,mul_nonneg hB.le (M n).hxs.le]
    have H := ((M n).alpha.val.property.2
      ((mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans (le_max_left _ _))).trans
      ((M n).regular z hz).2
    have HM := mul_le_mul_of_nonneg_left hzsize hcu.le
    dsimp only [Cm]
    nlinarith only [H,HM,(M n).hxs]
  obtain ⟨Cs,Q,hCs,hQ,Hclock,Hz⟩ := actual_selected_bad_history_radius_clock_control_along_weak_general
    Cm 0 B hCm hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G hx htotal Hupper
  obtain ⟨CP,hCP,HP⟩ := comparison_scalar_compact_response_eventually_bounded
    (fun n=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs) g
    (hG Q hQ) (hg Q hQ)
  let Cbig := max Cm B
  have hbig : 0 < Cbig := hCm.trans_le (le_max_left _ _)
  obtain ⟨CR,hCR,HR⟩ := exists_actual_selected_bad_history_radius_scalar_gap_uniform_along_weak_general
    c Cbig hc hbig hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure
    dim M hx hlarge 0 B le_rfl hB Gamma T hTemp
  refine ⟨2*|T| *(CP+CR)+2,by positivity,?_⟩
  filter_upwards [Hsmall,Hupper,Hclock,HP,HR,Hclosure,
    (Metric.tendstoUniformlyOn_iff.mp Hz) 1 zero_lt_one]
    with n hs hu hclock hp hr hclosure hz t ht hlo
  obtain ⟨htotalN,hr⟩ := hr
  have hstrip : (M n).xs*t∈(M n).actualRadiusTargetStrip c Cbig := by
    refine ⟨⟨mul_nonneg (M n).hxs.le ht.1,le_min ?_ ?_⟩,hlo,?_⟩
    · exact (mul_le_mul_of_nonneg_left (ht.2.trans (le_max_right _ _)) (M n).hxs.le).trans_eq (mul_comm _ _)
    · exact (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs
    · exact (hu t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (M n).hxs.le)
  have hP := hp _ (hclock t ht).2.2
  have hR : |(S n t-Gamma n (K n t))/(M n).xs^3| ≤ CR := hr _ hstrip
  have hZ : |(((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
      (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3| ≤ 1 := by
    simpa only [Real.dist_eq,zero_sub,abs_neg,S] using (hz t ht).le
  have H := comparison_scalar_density_error_bound (g:=0) (by
    simpa only [mul_div_assoc] using (hclosure t ht).2)
  simp only [mul_zero,sub_zero] at H
  have HPmul := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2*|T| by positivity)
  have HRmul := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2*|T| by positivity)
  dsimp only [S,K] at hZ HRmul
  nlinarith only [H,HPmul,HRmul,hZ]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_virtual_gap_data_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfile (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q))
    (V : ℝ→ℝ) (hV : Monotone V) (hnegative : ∀t<0,V t=0)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    (hasupport : a∈comparisonIncrementSupport V) (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V) :
    Nonempty (ComparisonVirtualGapData g a b) := by
  have hTemp : 0 < T := G.hT
  have hmass : 0 < V ((a+b)/2) := comparison_increment_support_positive_cdf_after
    hV hnegative hasupport (by linarith)
  let c := V ((a+b)/2)/2
  let C := V ((a+b)/2)+1
  have hc : 0 < c := half_pos hmass
  have hC : 0 < C := by dsimp only [C];linarith
  have hB : 0 < B := (ha.trans_lt hab).trans hbB
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨KG,hKG,Hgradient⟩ := eventually_actual_history_high_gradient_uniform_above_mass_along_weak_general
    c B hc hB hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare htotal hlarge g hG hg
  let f := fun t=>-2*T*g t
  have hf : IntegrableOn f (Icc a b) :=
    (((hg b (ha.trans_lt hab)).mono (fun t ht=>⟨ha.trans ht.1,ht.2⟩)).integrableOn_Icc).const_mul _
  have Hlocal : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t →
      Tendsto (fun n=>∫r in Icc s t,|(M n).actualVirtualScaledGradient r-f r|) atTop (𝓝 0) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl|hst
    · simp
    have Hmass := actual_compact_gap_mass_band_along dim M V hV hCDF hab hgap hmass hs ht
    exact (actual_selected_bad_history_high_radius_gradient_L1_along_weak_general
      c C s t hc hC (ha.trans hs.1.le) hst hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare htotal Hmass hlarge g hG hg).2
  obtain ⟨K,hK,j,hj,hjbound,⟨P⟩⟩ := actual_virtual_gap_primitive_of_gradient_limit_along
    hdelta hcu.le hAz hC0 (by linarith) dim hdim M hx V hV hCDF ha hab hbB
    hasupport hbsupport hgap hmass f hf ⟨KG,hKG.le,Hgradient⟩ Hlocal
  refine ⟨P.toGap (Or.inl ?_)⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hjpos : 0 < j t :=
    (div_pos zero_lt_one (sq_pos_of_pos (zero_lt_one.trans_le hK))).trans_le
      (hjbound t ⟨ht.1.le,ht.2.le⟩).1
  dsimp only [f]
  constructor
  · intro hgt
    exact mul_neg_of_pos_of_neg hjpos (mul_neg_of_neg_of_pos (by linarith) hgt)
  · intro hgt
    exact mul_pos hjpos (mul_pos_of_neg_of_neg (by linarith) hgt)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_with_virtual_gaps_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal,
          ∀a b : ℝ,0 ≤ a → a < b →
            a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
            (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
            Nonempty (ComparisonVirtualGapData
              (comparisonLocalScalarLimitResponse (G.hT)
                T d.beta d.U d.sigma) a b) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,⟨d⟩⟩ := exists_actual_selected_bad_history_high_joint_scalar_limit_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim
    hcompare hlarge
  refine ⟨phi,hphi,htotal,d,?_⟩
  intro a b ha hab hasupport hbsupport hgap
  let hT : 0<T := G.hT
  let g := comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma
  have hg : ∀R : ℝ,0<R → ContinuousOn g (Icc (0:ℝ) R) := by
    intro R hR
    have Hi : IntegrableOn
        (comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma) (uIcc (0:ℝ) R) := by
      simpa only [uIcc_of_le hR.le] using (d.limits R hR).1.integrableOn_Icc
    change ContinuousOn (fun r=>∫s in 0..r,
      comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma s) (Icc (0:ℝ) R)
    simpa only [uIcc_of_le hR.le] using intervalIntegral.continuousOn_primitive_interval Hi
  exact actual_selected_bad_history_high_virtual_gap_data_along_weak_general (B:=b+1)
    ha hab (by linarith) hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    (hWlim.comp hphi.tendsto_atTop) (fun n=>hcompare (phi n)) htotal
    (hlarge.comp hphi.tendsto_atTop) g (fun R hR=>(d.limits R hR).2.2) hg
    d.V.mass d.V.monotone d.radius_negative_axis_zero d.radius_inverse_cdf_limit
    hasupport hbsupport hgap

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_linear_profile_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal,
          let kappa := (T/T)*scalarInitialDensityConstant
            (G.hT) d.beta
          (∀t>0,d.U.mass t=kappa*t) ∧ (∀t>0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,d,Hvirtual⟩ :=
    exists_actual_selected_bad_history_high_joint_scalar_limit_with_virtual_gaps_along_weak_general
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare hlarge
  have Hcan : Tendsto (fun n=>(M (phi n)).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    have H := hWlim.comp hphi.tendsto_atTop
    simpa only [Function.comp_def,hcanonical] using H
  have Hlinear := d.global_profile_rigidity_of_actual_history_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    (hdim.comp hphi.tendsto_atTop) Hcan (G.comp phi hphi) Hvirtual
  refine ⟨phi,hphi,htotal,d,Hlinear.1,Hlinear.2,?_⟩
  have hx : Tendsto (fun n=>(M (phi n)).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n=>(M (phi n)).hxs.le)
      (fun n=>(M (phi n)).canonical_direct_test_band_ge_scale) Hcan
  let t := max Az 1
  have ht : 0 < t := zero_lt_one.trans_le (le_max_right _ _)
  have Hgrowth := d.radius_outer_growth hAz hx t (le_max_left _ _)
  rw [Hlinear.2 t ht] at Hgrowth
  exact ⟨le_of_mul_le_mul_right Hgrowth.1 ht,le_of_mul_le_mul_right Hgrowth.2 ht⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_linear_profile_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal,
          let kappa := (T/T)*scalarInitialDensityConstant
            (G.hT) d.beta
          (∀t>0,d.U.mass t=kappa*t) ∧ (∀t>0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu := by
  have hTemp : 0 < T := G.hT
  let strength := fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2
  have hstrength : ∀n,0 ≤ strength n := fun n=>
    div_nonneg (laplaceComparisonStrength_nonneg (M n).context.d (M n).xs (M n).hlam.le)
      (sq_nonneg _)
  rcases nonnegative_sequence_bounded_or_divergent_subsequence strength hstrength with Hbound | Hlarge
  · obtain ⟨theta,htheta,K,hK,Hwork⟩ := Hbound
    obtain ⟨psi,hpsi,htotal,Hlimit⟩ :=
      exists_actual_selected_bad_history_bounded_linear_profile_along_weak_general K hK
        hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
        (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
        (fun n=>M (theta n)) (G.comp theta htheta) (fun n=>W (theta n))
        (fun n=>hcanonical (theta n)) (hWlim.comp htheta.tendsto_atTop)
        (fun n=>hcompare (theta n)) (Eventually.of_forall Hwork)
    exact ⟨theta ∘ psi,htheta.comp hpsi,htotal,Hlimit⟩
  · obtain ⟨theta,htheta,Hwork⟩ := Hlarge
    obtain ⟨psi,hpsi,htotal,Hlimit⟩ :=
      exists_actual_selected_bad_history_high_linear_profile_along_weak_general
        hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
        (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
        (fun n=>M (theta n)) (G.comp theta htheta) (fun n=>W (theta n))
        (fun n=>hcanonical (theta n)) (hWlim.comp htheta.tendsto_atTop)
        (fun n=>hcompare (theta n)) Hwork
    exact ⟨theta ∘ psi,htheta.comp hpsi,htotal,Hlimit⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem exists_actual_selected_bad_history_linear_profile_with_zero_scalar_limits_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃phi : ℕ → ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n => M (phi n)) htotal,
          let hT := G.hT
          let kappa := (T/T)*scalarInitialDensityConstant hT d.beta
          (∀t > 0,d.U.mass t=kappa*t) ∧ (∀t > 0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu ∧ d.sigma=0 ∧
            (∀t ≥ 0,comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t=0) ∧
            (∀t ≥ 0,comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma t=0) ∧
            ∀R : ℝ,0 < R →
              TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT T
                ((M (phi n)).inheritedScalarMassProfile hT (htotal n)) (M (phi n)).xs)
                (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
              TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
                (scalarCovarianceResponse hT ((M (phi n)).inheritedScalarMassProfile hT (htotal n)))
                T (M (phi n)).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,d,Hlinear⟩ := exists_actual_selected_bad_history_linear_profile_along_weak_general
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim hcompare
  have Hzero := d.scalar_primitives_zero_of_linear_profiles Hlinear.1 Hlinear.2.1
  exact ⟨phi,hphi,htotal,d,Hlinear.1,Hlinear.2.1,Hlinear.2.2.1,Hlinear.2.2.2,
    Hzero.1,Hzero.2.1,Hzero.2.2,
    d.compact_scalar_zero_limits_of_linear_profiles Hlinear.1 Hlinear.2.1⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_complete_direct_profile_along_weak_general
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃phi : ℕ → ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualInheritedLocalScalarLimitData
          (G.hT) T
          (fun n => M (phi n)) htotal,
          let hT := G.hT
          let kappa := (T/T)*scalarInitialDensityConstant hT d.beta
          (∀t > 0,d.U.mass t=kappa*t) ∧ (∀t > 0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu ∧
            2*T*Real.exp (-12*T) ≤ kappa ∧
            kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) ∧
            TendstoLocallyUniformlyOn
              (fun n v=>(M (phi n)).R ((M (phi n)).xs*v)/(M (phi n)).xs)
              (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧ d.sigma=0 ∧
            (∀t ≥ 0,comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t=0) ∧
            (∀t ≥ 0,comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma t=0) ∧
            ∀R : ℝ,0 < R →
              TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT T
                ((M (phi n)).inheritedScalarMassProfile hT (htotal n)) (M (phi n)).xs)
                (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
              TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
                (scalarCovarianceResponse hT ((M (phi n)).inheritedScalarMassProfile hT (htotal n)))
                T (M (phi n)).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup,Hsigma,Hslope,Hresponse,Hlimits⟩ :=
    exists_actual_selected_bad_history_linear_profile_with_zero_scalar_limits_along_weak_general
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W hcanonical hWlim
      hcompare
  have Hcan : Tendsto (fun n=>(M (phi n)).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    have H : Tendsto (fun n=>W (phi n)) atTop (𝓝 0) := hWlim.comp hphi.tendsto_atTop
    simpa only [hcanonical] using H
  have Hdensity := comparison_local_scalar_initial_density_uniform_bounds
    (G.hT) hTemp.le d.beta
  exact ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup,Hdensity.1,Hdensity.2,
    d.original_radius_locally_uniform_of_linear_profile hcl hklo Hcan HV,
    Hsigma,Hslope,Hresponse,Hlimits⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
