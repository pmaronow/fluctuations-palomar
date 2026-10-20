module

public import ComparisonNativeActualGeneralHistoryContext
public import ComparisonSignedCavityActualLowErrorSavingAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 10000000

theorem actual_weak_history_scalar_site_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0) :
    Tendsto (fun n=>1/((M n).context.N*(M n).xs)) atTop (𝓝 0) := by
  have H := (actual_low_error_omitted_site_ratio_tendsto_zero_along hm hC0 dim hdim M).mul G.xs_zero
  simp only [mul_zero] at H
  apply H.congr
  intro n
  change (1/(M n).context.N)/(M n).xs^2*(M n).xs = _
  field_simp [(M n).hxs.ne']

theorem actual_weak_history_strength_ratio_atTop_of_working_scale_lower
    {m delta cl cu Az C0 Ct D Bclock T c0 w0 : ℝ} {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ (M n).canonicalDirectTestBandScale) :
    Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  let L := max K 0+1
  have hL : 0 < L := by dsimp [L];positivity
  have hKL : K ≤ L := by dsimp [L];linarith [le_max_left K 0]
  have hcut : 0 < min w0 (w0/Real.sqrt L) := lt_min hw0 (div_pos hw0 (Real.sqrt_pos.mpr hL))
  filter_upwards [hWlower,G.xs_zero.eventually (gt_mem_nhds hcut)] with n hnW hnX
  have hxW : (M n).xs < w0 := hnX.trans_le (min_le_left _ _)
  have hsqrt : w0 ≤ Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) := by
    exact (le_max_iff.mp hnW).resolve_left (not_le.mpr hxW)
  have he := laplaceComparisonStrength_pos (M n).context.d (M n).hlam (M n).xs
  have heW : w0^2 ≤ laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs := by
    nlinarith [Real.sq_sqrt he.le]
  have hxL : (M n).xs*Real.sqrt L < w0 :=
    (lt_div_iff₀ (Real.sqrt_pos.mpr hL)).mp (hnX.trans_le (min_le_right _ _))
  have hxs := (M n).hxs
  have hLL : L*(M n).xs^2 ≤ w0^2 := by
    have H := pow_le_pow_left₀ (mul_nonneg hxs.le (Real.sqrt_nonneg L)) hxL.le 2
    rw [mul_pow,Real.sq_sqrt hL.le] at H
    nlinarith only [H]
  exact hKL.trans ((le_div_iff₀ (sq_pos_of_pos hxs)).mpr (hLL.trans heW))

theorem eventually_actual_weak_history_working_scale_le_one
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNativeProfileHistory M T c0)
    (hd : ∀ᶠn in atTop,(M n).context.d ≤ 1) :
    ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1 := by
  filter_upwards [hd,G.xs_zero.eventually (eventually_le_nhds zero_lt_one)] with n hnD hnX
  apply max_le hnX
  have H := Real.sqrt_le_sqrt
    ((laplaceComparisonStrength_le (M n).context.d (M n).hlam.le (M n).xs).trans (M n).hld)
  have Hsqrt : Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) ≤
      (M n).context.d := by
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos (M n).context.hd] using H
  exact Hsqrt.trans hnD

end OAI.SKFluctuations.LaplaceWindowFormalization
