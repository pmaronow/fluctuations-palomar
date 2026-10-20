module

public import SKProof.Port.ComparisonActualOriginalQTargetWeightedTailAlong
public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 12000000
namespace ActualThetaZeroOverlapMinimum

def targetGCutEnvelope {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (x Couter C R : ℝ) : ℝ :=
  C*((∫u in 0..min (Couter*M.directTestWorkingScale) 1,
      Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+
    3/M.data.N+R*M.directTestWorkingScale*
      ((∫u in 0..1,Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-
        (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2))+3/M.data.N))/x^2

theorem targetGCutEnvelope_nonneg {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℝ) {Couter C R : ℝ} (houter : 0 ≤ Couter) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    0 ≤ M.targetGCutEnvelope x Couter C R := by
  have hW := M.canonical_direct_test_band_pos
  have hlo : 0 ≤ ∫u in 0..min (Couter*M.directTestWorkingScale) 1,
      Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) :=
    intervalIntegral.integral_nonneg (le_min (mul_nonneg houter hW.le) zero_le_one)
      (fun _ _=>Real.sqrt_nonneg _)
  have hhi : 0 ≤ ∫u in (0:ℝ)..1,
      Real.sqrt (orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _=>Real.sqrt_nonneg _)
  unfold targetGCutEnvelope
  positivity

theorem actual_target_site_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n)
    (hWlim : Tendsto (fun n=>(M n).directTestWorkingScale) atTop (𝓝 0)) :
    Tendsto (fun n=>1/((M n).data.N*(x n)^2)) atTop (𝓝 0) := by
  have HW := hWlim.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  have Hpow : Tendsto (fun n=>C0^6*((dim n+1:ℕ):ℝ)^(-6*m)) atTop (𝓝 0) := by
    have HH := ((tendsto_rpow_neg_atTop (by positivity : 0 < 6*m)).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)).const_mul (C0^6)
    simpa only [Function.comp_def,mul_zero,neg_mul] using HH
  apply squeeze_zero' _ _ Hpow
  · filter_upwards [] with n
    have hx := (M n).hxs.trans_le (hxs n)
    positivity
  · filter_upwards [HW] with n hnW
    have hx := (M n).hxs
    have hx1 := (M n).canonical_direct_test_band_ge_scale.trans hnW
    have hfour : (M n).xs^4 ≤ 1 := pow_le_one₀ hx.le hx1
    have hsix : (M n).xs^6 ≤ (x n)^2 := by
      have HH := mul_le_mul_of_nonneg_right hfour (sq_nonneg (M n).xs)
      have Hxx : (M n).xs^2 ≤ (x n)^2 := by nlinarith [hxs n]
      nlinarith only [HH,Hxx]
    have Hcritical := (M n).canonical_high_mass_inverse_power hC0 6
    norm_num only [Nat.cast_ofNat,div_self (by norm_num : (6:ℝ) ≠ 0),Real.rpow_one] at Hcritical
    have Hle : 1/((M n).data.N*(x n)^2) ≤ 1/((M n).data.N*(M n).xs^6) :=
      div_le_div_of_nonneg_left zero_le_one (by positivity)
        (mul_le_mul_of_nonneg_left hsix (M n).data.hN.le)
    simpa only [ActualHighWallData.N] using Hle.trans Hcritical

theorem targetGCutEnvelope_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h (M n).data.rmin 1)
    (Homit : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).directTestWorkingScale) atTop (𝓝 0))
    (Couter C R : ℝ) (houter : 0 < Couter) :
    Tendsto (fun n=>(M n).targetGCutEnvelope (x n) Couter C R) atTop (𝓝 0) := by
  have HW1 := hWlim.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  have Hlo := regular_target_to_working_band_l1_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M x hxs hclock Homit Hcutoff hsmall hWlim Couter houter
    (fun _=>0) (fun n=>min (Couter*(M n).directTestWorkingScale) 1)
    (Eventually.of_forall (fun n=>⟨le_rfl,
      le_min (mul_pos houter (M n).canonical_direct_test_band_pos).le zero_le_one,le_rfl⟩))
  have Hhi := regular_target_weighted_high_l1_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs dim hdim M x hxs hxlim hclock Homit Hcutoff hsmall HW1
    (fun _=>0) (Eventually.of_forall (fun _=>⟨le_rfl,zero_le_one⟩))
  have Hsite := actual_target_site_ratio_tendsto_zero_along hm hC0 dim hdim M x hxs hWlim
  have Hscale := ((tendsto_const_nhds (x:=(1:ℝ))).add (hWlim.const_mul R)).const_mul (3:ℝ)
  have Hall := ((Hlo.add (Hhi.const_mul R)).add (Hscale.mul Hsite)).const_mul C
  simp only [mul_zero,add_zero] at Hall
  convert Hall using 1
  funext n
  unfold targetGCutEnvelope
  ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
