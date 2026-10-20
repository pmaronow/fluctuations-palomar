module

public import ComparisonNativeActualGeneralHistoryMacroscopicThermal
public import ComparisonNativeActualCoveredScalarGapIntegralAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal
namespace NativeOverlapMinimum
set_option maxHeartbeats 12000000

theorem actual_scalar_gap_site_ratio_tendsto_zero_of_scale_zero
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    Tendsto (fun n=>1/((M n).context.N*(M n).xs)) atTop (𝓝 0) := by
  have HW:=hxs.eventually (eventually_le_nhds zero_lt_one)
  have Hpow : Tendsto (fun n=>C0^6*((dim n+1:ℕ):ℝ)^(-6*m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,neg_mul] using
      ((tendsto_rpow_neg_atTop (by positivity : 0 < 6*m)).comp
        ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)).const_mul (C0^6)
  apply squeeze_zero' (Eventually.of_forall (fun n=>by
    have hx:=(M n).hxs
    have hN:=(M n).context.hN
    positivity)) _ Hpow
  filter_upwards [HW] with n hx1
  have hfive : (M n).xs^5 ≤ 1:=pow_le_one₀ (M n).hxs.le hx1
  have hsix : (M n).xs^6 ≤ (M n).xs := by
    nlinarith only [mul_le_mul_of_nonneg_right hfive (M n).hxs.le]
  have Hcritical:=(M n).canonical_high_mass_inverse_power hC0 6
  norm_num only [Nat.cast_ofNat,div_self (by norm_num : (6:ℝ) ≠ 0),Real.rpow_one] at Hcritical
  have Hle : 1/((M n).context.N*(M n).xs) ≤ 1/((M n).context.N*(M n).xs^6) :=
    div_le_div_of_nonneg_left zero_le_one (by have :=(M n).hxs; have :=(M n).context.hN; positivity)
      (mul_le_mul_of_nonneg_left hsix (M n).context.hN.le)
  simpa only [NativeOverlapContext.N] using Hle.trans Hcritical

theorem actual_original_low_error_density_tendsto_zero_of_full_thermal
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (A : ℝ) (hA : 0 < A) :
    Tendsto (fun n=>(M n).actualOriginalLowErrorDensitySaving A) atTop (𝓝 0) := by
  have Hinv : Tendsto (fun n=>1/((dim n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hsum:=Hfull.add Hinv
  simp only [add_zero] at Hsum
  apply squeeze_zero' (Eventually.of_forall (fun n=>(M n).actualOriginalLowErrorDensitySaving_pos hA |>.le)) _ Hsum
  filter_upwards [] with n
  let q:=min (A*(M n).canonicalDirectTestBandScale) 1
  have hq : q∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_pos hA (M n).canonical_direct_test_band_pos).le zero_le_one,min_le_right _ _⟩
  have Hmono:=intervalIntegral.integral_mono_interval le_rfl hq.1 hq.2
    (ae_of_all _ (fun u=>Real.sqrt_nonneg
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)))
    (native_intervalIntegrable_sqrt_of_intervalIntegrable (native_comparison_thermal_intervalIntegrable (M n)))
  exact add_le_add (div_le_div_of_nonneg_right Hmono (sq_nonneg (M n).xs)) le_rfl

theorem actual_original_scalar_gap_integral_envelope_of_full_thermal
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (err : ℕ→ℝ) (herr : ∀n,0 ≤ err n) (herrlim : Tendsto err atTop (𝓝 0)) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀n (T : ℝ) (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
        (star : ℝ),star∈Icc (0:ℝ) 1 →
        (∀u,0 < u → u ≤ A*(M n).xs → u < star →
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-scalarCovarianceResponse hT
            ((M n).inheritedScalarMassProfile hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
          C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
            (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(M n).context.N)+
              err n*(M n).xs^3) →
        (∫u in 0..min (A*(M n).xs) star,|orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|) ≤ eta n*(M n).xs^4 := by
  have HD:=actual_original_low_error_density_tendsto_zero_of_full_thermal dim hdim M Hfull A hA
  have HS:=actual_scalar_gap_site_ratio_tendsto_zero_of_scale_zero hm hC0 dim hdim M hxs
  have HE:=((HD.const_mul C).add (HS.const_mul (C*A))).add (herrlim.const_mul A)
  refine ⟨fun n=>(M n).originalScalarGapIntegralSaving A C (err n),
    fun n=>(M n).originalScalarGapIntegralSaving_nonneg hA hC (herr n),?_,?_⟩
  · simpa only [originalScalarGapIntegralSaving,mul_zero,add_zero,mul_one_div] using HE
  · intro n T hT htotal star hstar hpoint
    exact (M n).actual_original_scalar_gap_before_star_integral_le hT htotal hA hC (herr n) hstar hpoint

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
