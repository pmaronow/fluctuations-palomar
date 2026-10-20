module

public import ComparisonNativeActualScalarGapDensityIntegration
public import ComparisonNativeActualSelectedBadHistoryLowErrorDensityAlong
public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
set_option maxHeartbeats 8000000

theorem actual_scalar_gap_site_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    Tendsto (fun n=>1/((M n).context.N*(M n).xs)) atTop (𝓝 0) := by
  have HW := hWlim.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  have Hpow : Tendsto (fun n=>C0^6*((dim n+1:ℕ):ℝ)^(-6*m)) atTop (𝓝 0) := by
    have HH := ((tendsto_rpow_neg_atTop (by positivity : 0 < 6*m)).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)).const_mul (C0^6)
    simpa only [Function.comp_def,mul_zero,neg_mul] using HH
  apply squeeze_zero' _ _ Hpow
  · filter_upwards [] with n
    have hx := (M n).hxs
    have hN := (M n).context.hN
    positivity
  · filter_upwards [HW] with n hnW
    have hx := (M n).hxs
    have hx1 := (M n).canonical_direct_test_band_ge_scale.trans hnW
    have hfive : (M n).xs^5 ≤ 1 := pow_le_one₀ hx.le hx1
    have hsix : (M n).xs^6 ≤ (M n).xs := by
      have H := mul_le_mul_of_nonneg_right hfive hx.le
      nlinarith only [H]
    have Hcritical := (M n).canonical_high_mass_inverse_power hC0 6
    norm_num only [Nat.cast_ofNat,div_self (by norm_num : (6:ℝ) ≠ 0),Real.rpow_one] at Hcritical
    have Hle : 1/((M n).context.N*(M n).xs) ≤ 1/((M n).context.N*(M n).xs^6) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity)
        (mul_le_mul_of_nonneg_left hsix (M n).context.hN.le)
    simpa only [NativeOverlapContext.N] using Hle.trans Hcritical

theorem actual_selected_bad_history_scalar_gap_integral_saving_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (A C : ℝ) (hA : 0 < A) (err : ℕ → ℝ) (herrlim : Tendsto err atTop (𝓝 0)) :
    Tendsto (fun n=>(M n).originalScalarGapIntegralSaving A C (err n)) atTop (𝓝 0) := by
  have Hd := actual_selected_bad_history_original_low_error_density_saving_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim root M epsilon shell hb hh
    Hhistory hsmall hWlim A hA
  have Hs := actual_scalar_gap_site_ratio_tendsto_zero_along hm hC0 dim hdim M hWlim
  have H := ((Hd.const_mul C).add (Hs.const_mul (C*A))).add (herrlim.const_mul A)
  simpa only [originalScalarGapIntegralSaving,mul_zero,add_zero,mul_one_div] using H

theorem actual_selected_bad_history_original_scalar_gap_integral_envelope_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (err : ℕ → ℝ) (herr : ∀n,0 ≤ err n) (herrlim : Tendsto err atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ, (∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀n (T : ℝ) (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
        (star : ℝ), star ∈ Icc (0:ℝ) 1 →
        (∀u,0 < u → u ≤ A*(M n).xs → u < star →
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
            ((M n).inheritedScalarMassProfile hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
          C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
            (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(M n).context.N)+
              err n*(M n).xs^3) →
        (∫u in 0..min (A*(M n).xs) star,
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
            ((M n).inheritedScalarMassProfile hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|) ≤ eta n*(M n).xs^4 := by
  refine ⟨fun n=>(M n).originalScalarGapIntegralSaving A C (err n),
    fun n=>(M n).originalScalarGapIntegralSaving_nonneg hA hC (herr n),
    actual_selected_bad_history_scalar_gap_integral_saving_tendsto_zero_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim root M epsilon shell hb hh
      Hhistory hsmall hWlim A C hA err herrlim, ?_⟩
  intro n T hT htotal star hstar hpoint
  exact (M n).actual_original_scalar_gap_before_star_integral_le
    hT htotal hA hC (herr n) hstar hpoint

theorem actual_selected_bad_history_original_scalar_gap_integral_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (err : ℕ → ℝ) (herr : ∀n,0 ≤ err n) (herrlim : Tendsto err atTop (𝓝 0))
    (hT : 0 < T) (htotal : ∀n u,u∈Icc (0:ℝ) 1 → (M n).h u+(M n).b u ≤ T)
    (star : ℕ → ℝ) (hstar : ∀n,star n ∈ Icc (0:ℝ) 1)
    (hpoint : ∀ᶠn in atTop,∀u,0 < u → u ≤ A*(M n).xs → u < star n →
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
        ((M n).inheritedScalarMassProfile hT (htotal n))
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
      C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(M n).context.N)+
          err n*(M n).xs^3) :
    Tendsto (fun n=>(∫u in 0..min (A*(M n).xs) (star n),
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
        ((M n).inheritedScalarMassProfile hT (htotal n))
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/(M n).xs^4) atTop (𝓝 0) := by
  obtain ⟨eta,heta,hetalim,H⟩ :=
    actual_selected_bad_history_original_scalar_gap_integral_envelope_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim root M epsilon shell hb hh
      Hhistory hsmall hWlim A C hA hC err herr herrlim
  apply squeeze_zero' _ _ hetalim
  · filter_upwards [] with n
    apply div_nonneg
    · exact intervalIntegral.integral_nonneg
        (le_min (mul_pos hA (M n).hxs).le (hstar n).1) (fun _ _ => abs_nonneg _)
    · exact pow_nonneg (M n).hxs.le 4
  · filter_upwards [hpoint] with n hn
    exact (div_le_iff₀ (pow_pos (M n).hxs 4)).mpr
      (H n T hT (htotal n) (star n) (hstar n) hn)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
