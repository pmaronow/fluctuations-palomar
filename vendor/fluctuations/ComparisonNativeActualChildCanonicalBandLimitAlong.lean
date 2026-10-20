module

public import ComparisonNativeActualSelectedBadHistoryClocks
public import ComparisonNativeActualHighMassSharpScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock Ccal c0 : ℝ}

 theorem canonical_direct_test_band_le_calibrated_radius {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCcal : 0 ≤ Ccal)
    (hcompare : M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs) :
    M.canonicalDirectTestBandScale ≤ max Ccal 1*M.context.d := by
  have hxd : M.xs ≤ Ccal*M.context.d:=by
    apply (sq_le_sq₀ M.hxs.le (mul_nonneg hCcal M.context.hd.le)).mp
    have H:=hcompare.trans (mul_le_mul_of_nonneg_left
      ((laplaceComparisonStrength_le M.context.d M.hlam.le M.xs).trans M.hld) (sq_nonneg Ccal))
    nlinarith only [H]
  have hsqrt : Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs) ≤ M.context.d:=by
    have H:=Real.sqrt_le_sqrt ((laplaceComparisonStrength_le M.context.d M.hlam.le M.xs).trans M.hld)
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos M.context.hd] using H
  unfold canonicalDirectTestBandScale
  apply max_le
  · exact hxd.trans (mul_le_mul_of_nonneg_right (le_max_left Ccal 1) M.context.hd.le)
  · exact hsqrt.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_max_right Ccal 1) M.context.hd.le)

 theorem actual_canonical_band_tendsto_zero_of_radius_tendsto_along
    {N : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCcal : 0 ≤ Ccal)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hdlim : Tendsto (fun n=>(M n).context.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
  apply squeeze_zero (fun n=>(M n).canonical_direct_test_band_pos.le)
    (fun n=>(M n).canonical_direct_test_band_le_calibrated_radius hCcal (hcompare n))
  simpa only [mul_zero] using hdlim.const_mul (max Ccal 1)

theorem actual_selected_bad_child_canonical_band_tendsto_zero_along
    {N : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hxlim : Tendsto x atTop (𝓝 0))
    (hd : ∀ᶠn in atTop,(M n).context.d=actualChildRadius c0 (x n))
    (hCcal : 0 ≤ Ccal)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
  apply actual_canonical_band_tendsto_zero_of_radius_tendsto_along M hCcal hcompare
  have H:Tendsto (fun n=>c0*x n) atTop (𝓝 0):=by
    simpa only [mul_zero] using hxlim.const_mul c0
  apply H.congr'
  filter_upwards [hd] with n hn
  simpa only [actualChildRadius] using hn.symm

theorem ActualSelectedBadHistoryChain.radius_limit_or_eq_root
    {N : ℕ→ℕ}
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    Tendsto (fun n=>(M n).context.d) atTop (𝓝 0) ∨ M=root := by
  cases Hhistory with
  | root => exact Or.inr rfl
  | @child P M _history x _hx hxlim _htarget _hcap _hweak hd _hE _hb _hh =>
    apply Or.inl
    have H:Tendsto (fun n=>c0*x n) atTop (𝓝 0):=by
      simpa only [mul_zero] using hxlim.const_mul c0
    apply H.congr'
    filter_upwards [hd] with n hn
    simpa only [actualChildRadius] using hn.symm

 theorem ActualSelectedBadHistoryChain.canonical_band_limit_or_eq_root
    {N : ℕ→ℕ}
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hCcal : 0 ≤ Ccal)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) ∨ M=root := by
  rcases Hhistory.radius_limit_or_eq_root with hdlim|hroot
  · exact Or.inl (actual_canonical_band_tendsto_zero_of_radius_tendsto_along M hCcal hcompare hdlim)
  · exact Or.inr hroot

 theorem ActualSelectedBadHistoryChain.canonical_band_tendsto_zero_of_ne_root
    {N : ℕ→ℕ}
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) (hne : M≠root)
    (hCcal : 0 ≤ Ccal)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
  rcases Hhistory.canonical_band_limit_or_eq_root hCcal hcompare with H|H
  · exact H
  · exact False.elim (hne H)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
