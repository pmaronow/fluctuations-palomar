module

public import ComparisonNativeActualRadiusScalarModulus
public import ComparisonNativeActualRadiusStripIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal
namespace NativeOverlapMinimum
set_option maxHeartbeats 8000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem radius_absolute_cubic_rescaling (f : ℝ→ℝ)
    {a b x : ℝ} (hab : a ≤ b) (hx : 0 < x) :
    (∫t in Icc a b,|f (x*t)/x^3|)=(∫r in Icc (x*a) (x*b),|f r|)/x^4 := by
  simp_rw [abs_div,abs_of_pos (pow_pos hx 3)]
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_div,intervalIntegral.integral_comp_mul_left (fun r=>|f r|) hx.ne',
    intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le),
    ←integral_Icc_eq_integral_Ioc,smul_eq_mul]
  field_simp

theorem radius_scalar_residual_compact_integral_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {c C a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbC : b ≤ C)
    (hb1 : M.xs*b ≤ 1)
    (hmass : ∀t∈Icc a b,c*M.xs ≤ M.alpha.val.val (M.xs*t) ∧
      M.alpha.val.val (M.xs*t) ≤ C*M.xs)
    (f : ℝ→ℝ) (hf : IntegrableOn f (M.actualRadiusTargetStrip c C)) :
    (∫t in Icc a b,|f (M.xs*t)/M.xs^3|) ≤
      (∫r in M.actualRadiusTargetStrip c C,|f r|)/M.xs^4 := by
  have hsub : Icc (M.xs*a) (M.xs*b) ⊆ M.actualRadiusTargetStrip c C := by
    intro r hr
    have ht : r/M.xs∈Icc a b := by
      constructor
      · exact (le_div_iff₀ M.hxs).mpr (by simpa only [mul_comm] using hr.1)
      · exact (div_le_iff₀ M.hxs).mpr (by simpa only [mul_comm] using hr.2)
    have heq : M.xs*(r/M.xs)=r:=mul_div_cancel₀ r M.hxs.ne'
    have H:=hmass (r/M.xs) ht
    rw [heq] at H
    exact ⟨⟨(mul_nonneg M.hxs.le ha).trans hr.1,
      le_min (hr.2.trans (by nlinarith only [mul_le_mul_of_nonneg_left hbC M.hxs.le]))
        (hr.2.trans hb1)⟩,H⟩
  have H := setIntegral_mono_set hf.abs
    (Eventually.of_forall (fun r=>abs_nonneg (f r))) (Eventually.of_forall hsub)
  rw [radius_absolute_cubic_rescaling f hab M.hxs]
  exact div_le_div_of_nonneg_right H (pow_nonneg M.hxs.le 4)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
