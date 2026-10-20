module

public import ComparisonNativeActualLowErrorDensityProducer
public import ComparisonNativeActualInheritedClocks
public import ComparisonNativeActualMeanRawUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
set_option maxHeartbeats 8000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem original_scalar_gap_intervalIntegrable
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (alpha : boundedMassProfiles) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun u => orderedPathS (n+1) M.bf M.hf u -
      scalarCovarianceResponse hT alpha (actualMixedClock (n+1) M.bf M.hf u)) volume 0 q := by
  have hsub : uIcc (0:ℝ) q ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hq.1]
    exact Icc_subset_Icc le_rfl hq.2
  have hs : IntervalIntegrable (orderedPathS (n+1) M.bf M.hf) volume 0 q :=
    (M.mass_mean_monotone.mono hsub).intervalIntegrable
  have hK : MonotoneOn (actualMixedClock (n+1) M.bf M.hf) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (M.inherited_hf_monotone hu hv huv)
      (mul_le_mul (M.inherited_bf_monotone hu hv huv)
        (M.mass_mean_monotone hu hv huv) (M.mass_mean_nonneg hu) (NNReal.coe_nonneg _))
  have hki : IntervalIntegrable (fun u => actualMixedClock (n+1) M.bf M.hf u/T) volume 0 q :=
    (hK.mono hsub).intervalIntegrable.div_const T
  have he : IntervalIntegrable (fun u => scalarPlantedEnergy hT alpha
      (actualMixedClock (n+1) M.bf M.hf u/T)) volume 0 q := by
    rw [intervalIntegrable_iff, uIoc_of_le hq.1]
    apply Integrable.of_bound
      ((scalarPlantedEnergy_continuous hT alpha).comp_aestronglyMeasurable
        hki.1.aestronglyMeasurable) 1
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (scalarPlantedEnergy_bounds hT alpha _).1]
    exact (scalarPlantedEnergy_bounds hT alpha _).2
  exact hs.sub he

def originalScalarGapIntegralSaving
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (A C e : ℝ) : ℝ :=
  C*M.actualOriginalLowErrorDensitySaving A+C*A/(M.context.N*M.xs)+A*e

theorem originalScalarGapIntegralSaving_nonneg
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {A C e : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e) :
    0 ≤ M.originalScalarGapIntegralSaving A C e := by
  have hd := (M.actualOriginalLowErrorDensitySaving_pos hA).le
  have hx := M.hxs
  have hN := M.context.hN
  unfold originalScalarGapIntegralSaving
  positivity

theorem actual_density_pointwise_modulus_integral_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {A C e q : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hq : q ∈ Icc (0:ℝ) 1) (hqA : q ≤ A*M.xs)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 q)
    (hpoint : ∀u ∈ Ioo (0:ℝ) q, |f u| ≤ C*M.xs^2*
      (Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3) :
    (∫u in 0..q, |f u|) ≤ M.originalScalarGapIntegralSaving A C e*M.xs^4 := by
  let Q := min (A*M.canonicalDirectTestBandScale) 1
  have hQ : Q ∈ Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hA M.canonical_direct_test_band_pos).le zero_le_one, min_le_right _ _⟩
  have hqQ : q ≤ Q := le_min
    (hqA.trans (mul_le_mul_of_nonneg_left M.canonical_direct_test_band_ge_scale hA.le)) hq.2
  have hDI := native_intervalIntegrable_sqrt_of_intervalIntegrable
    (native_comparison_thermal_intervalIntegrable M)
  have hDQ := hDI.mono_set (show uIcc (0:ℝ) Q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hQ.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hQ.2)
  have hDq := hDI.mono_set (show uIcc (0:ℝ) q ⊆ uIcc 0 1 by
    rw [uIcc_of_le hq.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  have hDle : (∫u in 0..q, Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2)) ≤
      M.actualOriginalLowErrorDensitySaving A*M.xs^2 := by
    have hmono := intervalIntegral.integral_mono_interval le_rfl hq.1 hqQ
      (ae_of_all _ (fun _ => Real.sqrt_nonneg _)) hDQ
    apply hmono.trans
    unfold actualOriginalLowErrorDensitySaving
    rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 M.hxs.ne')]
    have hsite : 0 ≤ (1/((n+1:ℕ):ℝ))*M.xs^2 := by positivity
    linarith
  have hbound : (∫u in 0..q, |f u|) ≤
      ∫u in 0..q, C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3 := by
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
    (mul_nonneg (mul_nonneg hC (sq_nonneg M.xs)) (by positivity : 0 ≤ 1/M.context.N))
  have h3 := mul_le_mul_of_nonneg_right hqA (mul_nonneg he (pow_nonneg M.hxs.le 3))
  have hx := M.hxs.ne'
  have hN := M.context.hN.ne'
  have hid : M.originalScalarGapIntegralSaving A C e*M.xs^4 =
      C*M.xs^2*(M.actualOriginalLowErrorDensitySaving A*M.xs^2)+
        (C*M.xs^2*(1/M.context.N))*(A*M.xs)+(A*M.xs)*(e*M.xs^3) := by
    unfold originalScalarGapIntegralSaving
    field_simp
  rw [hid]
  nlinarith only [hbound, h1, h2, h3]

theorem actual_original_scalar_gap_before_star_integral_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {A C e star : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hstar : star ∈ Icc (0:ℝ) 1)
    (hpoint : ∀u, 0 < u → u ≤ A*M.xs → u < star →
      |orderedPathS (n+1) M.bf M.hf u-scalarCovarianceResponse hT
        (M.inheritedScalarMassProfile hT htotal) (actualMixedClock (n+1) M.bf M.hf u)| ≤
        C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3) :
    (∫u in 0..min (A*M.xs) star, |orderedPathS (n+1) M.bf M.hf u-
      scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
        (actualMixedClock (n+1) M.bf M.hf u)|) ≤
      M.originalScalarGapIntegralSaving A C e*M.xs^4 := by
  have hq : min (A*M.xs) star ∈ Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hA M.hxs).le hstar.1, (min_le_right _ _).trans hstar.2⟩
  apply M.actual_density_pointwise_modulus_integral_le hA hC he hq (min_le_left _ _) _
    (M.original_scalar_gap_intervalIntegrable hT _ hq)
  intro u hu
  exact hpoint u hu.1 (hu.2.le.trans (min_le_left _ _)) (hu.2.trans_le (min_le_right _ _))

theorem actual_original_scalar_gap_covered_integral_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {A C e star : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hstar : star ∈ Icc (0:ℝ) 1) (hcover : A*M.xs ≤ star)
    (hpoint : ∀u, 0 < u → u ≤ A*M.xs → u < star →
      |orderedPathS (n+1) M.bf M.hf u-scalarCovarianceResponse hT
        (M.inheritedScalarMassProfile hT htotal) (actualMixedClock (n+1) M.bf M.hf u)| ≤
        C*M.xs^2*(Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)+1/M.context.N)+e*M.xs^3) :
    (∫u in 0..A*M.xs, |orderedPathS (n+1) M.bf M.hf u-
      scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
        (actualMixedClock (n+1) M.bf M.hf u)|) ≤
      M.originalScalarGapIntegralSaving A C e*M.xs^4 := by
  simpa only [min_eq_left hcover] using M.actual_original_scalar_gap_before_star_integral_le
    hT htotal hA hC he hstar hpoint

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
