module

public import ComparisonSignedCavityOriginalInheritedConstantEndpoints
public import ComparisonNativeActualScalarGapDensityIntegration
public import SKProof.Port.ComparisonActualOriginalQLowDensitySourceAlong
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_continuum_retained_scalar_pair_tendsto
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T)
    (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k=>nativeOriginalScalarPairMean (finiteCutMasses us k)
      (nativeContinuumMixedClock n M.sweepBf M.sweepHf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
        (actualMixedClock (n+1) M.sweepBf M.sweepHf u.val))) :=
  continuum_retained_scalar_pair_tendsto n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu

theorem inherited_continuum_retained_scalar_mean_gap_tendsto
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T)
    (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k=>
      finitePhysicalMean (n+1) (finiteCutMasses us k)
        (retainedStarMatrix M.sweepBf (finiteCutMasses us k))
        (retainedStarField M.sweepHf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))-
      nativeOriginalScalarPairMean (finiteCutMasses us k)
        (nativeContinuumMixedClock n M.sweepBf M.sweepHf (finiteCutMasses us k))
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (orderedPathS (n+1) M.sweepBf M.sweepHf u.val-
        scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
          (actualMixedClock (n+1) M.sweepBf M.sweepHf u.val))) :=
  continuum_retained_scalar_mean_gap_tendsto n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu

def originalScalarGapIntegralSaving
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (A C e : ℝ) : ℝ :=
  C*M.actualOriginalLowErrorDensitySaving A+C*A/(M.data.N*M.xs)+A*e

theorem originalScalarGapIntegralSaving_nonneg
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {A C e : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e) :
    0 ≤ M.originalScalarGapIntegralSaving A C e := by
  have hd := (M.actualOriginalLowErrorDensitySaving_pos hA).le
  have hx := M.hxs
  have hN := M.data.hN
  unfold originalScalarGapIntegralSaving
  positivity

theorem actual_density_pointwise_modulus_integral_le
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {A C e q : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hq : q ∈ Icc (0:ℝ) 1) (hqA : q ≤ A*M.xs)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 q)
    (hpoint : ∀u ∈ Ioo (0:ℝ) q, |f u| ≤ C*M.xs^2*
      (Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
        (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2)+1/M.data.N)+e*M.xs^3) :
    (∫u in 0..q, |f u|) ≤ M.originalScalarGapIntegralSaving A C e*M.xs^4 := by
  let Q := min (A*M.directTestWorkingScale) 1
  have hQ : Q ∈ Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hA M.canonical_direct_test_band_pos).le zero_le_one, min_le_right _ _⟩
  have hqQ : q ≤ Q := le_min
    (hqA.trans (mul_le_mul_of_nonneg_left M.canonical_direct_test_band_ge_scale hA.le)) hq.2
  have hDI := native_intervalIntegrable_sqrt_of_intervalIntegrable
    (M.original_thermal_intervalIntegrable)
  have hDQ := hDI.mono_set (show uIcc (0:ℝ) Q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hQ.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hQ.2)
  have hDq := hDI.mono_set (show uIcc (0:ℝ) q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  have hDle : (∫u in 0..q, Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
      (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2)) ≤
      M.actualOriginalLowErrorDensitySaving A*M.xs^2 := by
    have hmono := intervalIntegral.integral_mono_interval le_rfl hq.1 hqQ
      (ae_of_all _ (fun _ => Real.sqrt_nonneg _)) hDQ
    apply hmono.trans
    unfold actualOriginalLowErrorDensitySaving
    rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 M.hxs.ne')]
    have hsite : 0 ≤ (1/((n+1:ℕ):ℝ))*M.xs^2 := by positivity
    linarith
  have hbound : (∫u in 0..q, |f u|) ≤
      ∫u in 0..q, C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
        (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2)+1/M.data.N)+e*M.xs^3 := by
    apply intervalIntegral.integral_mono_ae_restrict hq.1 hf.abs
      (((hDq.add intervalIntegrable_const).const_mul _).add intervalIntegrable_const)
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0:ℝ)), ae_restrict_of_ae (volume.ae_ne q)]
      with u hu hu0 huq
    exact hpoint u ⟨lt_of_le_of_ne hu.1 hu0.symm, lt_of_le_of_ne hu.2 huq⟩
  rw [intervalIntegral.integral_add ((hDq.add intervalIntegrable_const).const_mul _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hDq intervalIntegrable_const] at hbound
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
  have h1 := mul_le_mul_of_nonneg_left hDle (mul_nonneg hC (sq_nonneg M.xs))
  have h2 := mul_le_mul_of_nonneg_left hqA
    (mul_nonneg (mul_nonneg hC (sq_nonneg M.xs)) (by positivity : 0 ≤ 1/M.data.N))
  have h3 := mul_le_mul_of_nonneg_right hqA (mul_nonneg he (pow_nonneg M.hxs.le 3))
  have hx := M.hxs.ne'
  have hN := M.data.hN.ne'
  have hid : M.originalScalarGapIntegralSaving A C e*M.xs^4 =
      C*M.xs^2*(M.actualOriginalLowErrorDensitySaving A*M.xs^2)+
        (C*M.xs^2*(1/M.data.N))*(A*M.xs)+(A*M.xs)*(e*M.xs^3) := by
    unfold originalScalarGapIntegralSaving
    field_simp
  rw [hid]
  nlinarith only [hbound, h1, h2, h3]

theorem actual_original_scalar_gap_before_star_integral_le
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {A C e star : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hstar : star ∈ Icc (0:ℝ) 1)
    (hpoint : ∀u, 0 < u → u ≤ A*M.xs → u < star →
      |orderedPathS (n+1) M.sweepBf M.sweepHf u-scalarCovarianceResponse hT
        (M.inheritedScalarMassProfileBare hT htotal) (actualMixedClock (n+1) M.sweepBf M.sweepHf u)| ≤
        C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
          (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2)+1/M.data.N)+e*M.xs^3) :
    (∫u in 0..min (A*M.xs) star, |orderedPathS (n+1) M.sweepBf M.sweepHf u-
      scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
        (actualMixedClock (n+1) M.sweepBf M.sweepHf u)|) ≤
      M.originalScalarGapIntegralSaving A C e*M.xs^4 := by
  have hq : min (A*M.xs) star ∈ Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hA M.hxs).le hstar.1, (min_le_right _ _).trans hstar.2⟩
  apply M.actual_density_pointwise_modulus_integral_le hA hC he hq (min_le_left _ _) _
    (M.original_scalar_gap_intervalIntegrable hT _ hq)
  intro u hu
  exact hpoint u hu.1 (hu.2.le.trans (min_le_left _ _)) (hu.2.trans_le (min_le_right _ _))

theorem actual_original_scalar_gap_covered_integral_le
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {A C e star : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hstar : star ∈ Icc (0:ℝ) 1) (hcover : A*M.xs ≤ star)
    (hpoint : ∀u, 0 < u → u ≤ A*M.xs → u < star →
      |orderedPathS (n+1) M.sweepBf M.sweepHf u-scalarCovarianceResponse hT
        (M.inheritedScalarMassProfileBare hT htotal) (actualMixedClock (n+1) M.sweepBf M.sweepHf u)| ≤
        C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
          (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2)+1/M.data.N)+e*M.xs^3) :
    (∫u in 0..A*M.xs, |orderedPathS (n+1) M.sweepBf M.sweepHf u-
      scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
        (actualMixedClock (n+1) M.sweepBf M.sweepHf u)|) ≤
      M.originalScalarGapIntegralSaving A C e*M.xs^4 := by
  simpa only [min_eq_left hcover] using M.actual_original_scalar_gap_before_star_integral_le
    hT htotal hA hC he hstar hpoint

theorem actual_scalar_gap_site_ratio_tendsto_zero_along_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hWlim : Tendsto (fun n=>(M n).directTestWorkingScale) atTop (𝓝 0)) :
    Tendsto (fun n=>1/((M n).data.N*(M n).xs)) atTop (𝓝 0) := by
  have HW := hWlim.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  have Hpow : Tendsto (fun n=>C0^6*((dim n+1:ℕ):ℝ)^(-6*m)) atTop (𝓝 0) := by
    have HH := ((tendsto_rpow_neg_atTop (by positivity : 0 < 6*m)).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)).const_mul (C0^6)
    simpa only [Function.comp_def,mul_zero,neg_mul] using HH
  apply squeeze_zero' _ _ Hpow
  · filter_upwards [] with n
    have hx := (M n).hxs
    have hN := (M n).data.hN
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
    have Hle : 1/((M n).data.N*(M n).xs) ≤ 1/((M n).data.N*(M n).xs^6) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity)
        (mul_le_mul_of_nonneg_left hsix (M n).data.hN.le)
    simpa only [ActualHighWallData.N] using Hle.trans Hcritical

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
