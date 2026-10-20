module

public import ComparisonActualHighWallCriticalUnconditionalCenteringCaps
public import ComparisonNativeActualInitialMassError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 10000000

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_mean_radius_l1_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-
        (M n).data.wallRadius (M n).alpha u|)/(M n).xs^2) atTop (𝓝 0) := by
  let C' := max C 1
  have hC' : 1 ≤ C' := le_max_right _ _
  have HC' := actual_high_wall_critical_centering_l2_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hxlim hsRatio C' hC'
  have HCcut : ∀ᶠn in atTop,C'*(M n).xs≤1 :=
    (hxlim.const_mul C').eventually
      (eventually_le_nhds (show C'*(0:ℝ)<1 by simp))
  have HC : Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-
        (M n).data.wallRadius (M n).alpha u)^2)/(M n).xs^3) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ HC'
    · filter_upwards [] with n
      exact div_nonneg (intervalIntegral.integral_nonneg (mul_nonneg hC.le (M n).hxs.le)
        (fun _ _=>sq_nonneg _)) (pow_nonneg (M n).hxs.le 3)
    · filter_upwards [HCcut] with n hnCut
      apply div_le_div_of_nonneg_right _ (pow_nonneg (M n).hxs.le 3)
      apply intervalIntegral.integral_mono_interval le_rfl
        (mul_nonneg hC.le (M n).hxs.le)
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (M n).hxs.le)
        (ae_of_all _ (fun _=>sq_nonneg _))
      exact (M n).full_mass_squared_mismatch_intervalIntegrable.mono_set (by
        rw [uIcc_of_le (mul_nonneg (zero_le_one.trans hC') (M n).hxs.le),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hnCut)
  have Hlimit:=(HC.const_mul C).sqrt
  simp only [mul_zero,Real.sqrt_zero] at Hlimit
  have HW:=(hxlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
  apply squeeze_zero' _ _ Hlimit
  · filter_upwards [] with n
    exact div_nonneg (intervalIntegral.integral_nonneg (mul_nonneg hC.le (M n).hxs.le)
      (fun _ _=>abs_nonneg _)) (sq_nonneg _)
  · filter_upwards [HW] with n hnW
    have hw:=(M n).hxs
    have hi:=((M n).full_mass_squared_mismatch_intervalIntegrable).mono_set (by
      rw [uIcc_of_le (mul_nonneg hC.le (M n).hxs.le),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    have Hsq:=interval_integral_sqrt_sq_le (mul_nonneg hC.le (M n).hxs.le) hi
      (fun _ _=>sq_nonneg _)
    simp only [Real.sqrt_sq_eq_abs] at Hsq
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos (pow_pos hw 2) 2)).mpr
    convert Hsq using 1; field_simp [hw.ne']

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
