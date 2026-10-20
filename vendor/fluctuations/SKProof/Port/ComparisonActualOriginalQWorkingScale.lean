module

public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import ComparisonNativeActualComparableBandWorkingScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
theorem actual_low_error_omitted_site_ratio_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    (1/(n+1:ℕ):ℝ)/a.xs^2 ≤ C0^2*a.data.N^(-((2:ℝ)/3+2*m)) := by
  have H:=a.canonical_high_mass_inverse_power hC0 2
  simp only [Nat.cast_ofNat,show (2:ℝ)/6=(1:ℝ)/3 by norm_num] at H
  have HM:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.data.hN.le (-((2:ℝ)/3)))
  have HE : a.data.N^(-((2:ℝ)/3))=a.data.N^((1:ℝ)/3)/a.data.N := by
    calc
      _=a.data.N^(((1:ℝ)/3)-1) := by congr 1;ring
      _=a.data.N^((1:ℝ)/3)/a.data.N^((1:ℝ)) := Real.rpow_sub a.data.hN _ _
      _=_ := by rw [Real.rpow_one]
  have HL : a.data.N^(-((2:ℝ)/3))*(1/(a.data.N^((1:ℝ)/3)*a.xs^2))=
      (1/(n+1:ℕ):ℝ)/a.xs^2 := by
    rw [HE]
    have hpow : a.data.N^((1:ℝ)/3)≠0:=(Real.rpow_pos_of_pos a.data.hN _).ne'
    have hx:=a.hxs.ne'
    have hN:=a.data.hN.ne'
    change _=(1/a.data.N)/a.xs^2
    field_simp
  have HR : a.data.N^(-((2:ℝ)/3))*(C0^2*a.data.N^(-(2:ℝ)*m))=
      C0^2*a.data.N^(-((2:ℝ)/3+2*m)) := by
    rw [mul_left_comm,←Real.rpow_add a.data.hN]
    congr 2
    ring
  rw [HL,HR] at HM
  exact HM

theorem actual_low_error_omitted_site_ratio_tendsto_zero_along_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n=>(1/(dim n+1:ℕ):ℝ)/(a n).xs^2) atTop (𝓝 0) := by
  have Hpow:=(tendsto_rpow_neg_atTop (show 0 < (2:ℝ)/3+2*m by positivity)).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Hlim:=Hpow.const_mul (C0^2)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n=>by have hx:=(a n).hxs;positivity)
    (fun n=>actual_low_error_omitted_site_ratio_le_original_q (a n) hC0)
  simpa only [ActualHighWallData.N,Function.comp_def] using Hlim

end ActualThetaZeroOverlapMinimum
theorem actual_comparable_context_scalar_site_ratio_tendsto_zero_original_q
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T) :
    Tendsto (fun n=>1/((M n).data.N*(M n).xs)) atTop (𝓝 0) := by
  have H := (ActualThetaZeroOverlapMinimum.actual_low_error_omitted_site_ratio_tendsto_zero_along_original_q hm hC0 dim hdim M).mul G.xs_zero
  simp only [mul_zero] at H
  apply H.congr
  intro n
  change (1/(M n).data.N)/(M n).xs^2*(M n).xs = _
  field_simp [(M n).hxs.ne']

theorem actual_comparable_context_strength_ratio_atTop_of_working_scale_lower_original_q
    {m delta cl cu Az C0 Ct D Bclock T w0 : ℝ} {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ (M n).directTestWorkingScale) :
    Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  let L := max K 0+1
  have hL : 0 < L := by dsimp [L];positivity
  have hKL : K ≤ L := by dsimp [L];linarith [le_max_left K 0]
  have hcut : 0 < min w0 (w0/Real.sqrt L) := lt_min hw0 (div_pos hw0 (Real.sqrt_pos.mpr hL))
  filter_upwards [hWlower,G.xs_zero.eventually (gt_mem_nhds hcut)] with n hnW hnX
  have hxW : (M n).xs < w0 := hnX.trans_le (min_le_left _ _)
  have hsqrt : w0 ≤ Real.sqrt (laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) := by
    exact (le_max_iff.mp hnW).resolve_left (not_le.mpr hxW)
  have he := laplaceComparisonStrength_pos (M n).data.d (M n).hlam (M n).xs
  have heW : w0^2 ≤ laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs := by
    nlinarith [Real.sq_sqrt he.le]
  have hxL : (M n).xs*Real.sqrt L < w0 :=
    (lt_div_iff₀ (Real.sqrt_pos.mpr hL)).mp (hnX.trans_le (min_le_right _ _))
  have hxs := (M n).hxs
  have hLL : L*(M n).xs^2 ≤ w0^2 := by
    have H := pow_le_pow_left₀ (mul_nonneg hxs.le (Real.sqrt_nonneg L)) hxL.le 2
    rw [mul_pow,Real.sq_sqrt hL.le] at H
    nlinarith only [H]
  exact hKL.trans ((le_div_iff₀ (sq_pos_of_pos hxs)).mpr (hLL.trans heW))

theorem eventually_actual_comparable_context_working_scale_le_one_original_q
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hd : ∀ᶠn in atTop,(M n).data.d ≤ 1) :
    ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1 := by
  filter_upwards [hd,G.xs_zero.eventually (eventually_le_nhds zero_lt_one)] with n hnD hnX
  apply max_le hnX
  have H := Real.sqrt_le_sqrt
    ((laplaceComparisonStrength_le (M n).data.d (M n).hlam.le (M n).xs).trans (M n).hld)
  have Hsqrt : Real.sqrt (laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) ≤
      (M n).data.d := by
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos (M n).data.hd] using H
  exact Hsqrt.trans hnD

end OAI.SKFluctuations.LaplaceWindowFormalization
