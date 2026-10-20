module

public import SKProof.Port.ComparisonActualOriginalQHighInitialMassMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum

theorem actual_HIGH_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      |orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u|)/((M n).xs)^2)
      atTop (𝓝 0) := by
  have Hsquare:=actual_HIGH_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G hlarge C hC
  have Hlimit:=(Hsquare.const_mul C).sqrt
  simp only [mul_zero,Real.sqrt_zero] at Hlimit
  have HW:=(G.xs_zero.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Hlimit
  · filter_upwards [] with n
    have hw:=(M n).hxs
    exact div_nonneg (intervalIntegral.integral_nonneg (by positivity)
      (fun u _=>abs_nonneg _)) (sq_nonneg _)
  · filter_upwards [HW] with n hnW
    have hw:=(M n).hxs
    have hi:=((M n).mass_squared_mismatch_intervalIntegrable).mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ C*(M n).xs),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    have Hsq:=interval_integral_sqrt_sq_le (by positivity : 0 ≤ C*(M n).xs) hi
      (fun u _=>sq_nonneg _)
    simp only [Real.sqrt_sq_eq_abs] at Hsq
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos (pow_pos hw 2) 2)).mpr
    convert Hsq using 1; field_simp [hw.ne']

theorem actual_HIGH_original_retained_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop)
    (v : ℕ→ℝ)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*(M n).xs) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf w-(M n).sweepRadius w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/((M n).xs)^3) atTop (𝓝 0) := by
  have Hfull:=actual_HIGH_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G hlarge C hC
  have HW:=(G.xs_zero.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Hfull
  · filter_upwards [] with n
    have hw:=(M n).hxs
    exact div_nonneg (integral_nonneg (fun _=>sq_nonneg _)) (pow_pos hw 3).le
  · filter_upwards [HW] with n hnW
    have hw:=(M n).hxs
    rw [comparison_original_retained_integral_eq_interval (hv n)
      (fun u=>(orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u)^2)]
    apply div_le_div_of_nonneg_right _ (pow_pos hw 3).le
    have hi:=((M n).mass_squared_mismatch_intervalIntegrable).mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ C*(M n).xs),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    exact intervalIntegral.integral_mono_interval le_rfl (hv n).1 (hvc n)
      (ae_of_all _ (fun _=>sq_nonneg _)) hi

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
