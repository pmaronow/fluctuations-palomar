module

public import ComparisonSignedCavityActualMinimumResampling

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization
set_option maxHeartbeats 4000000

theorem observed_log_succ_le_twice {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n+1:ℕ):ℝ) ≤ 2*Real.log (n:ℝ) := by
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have H := Real.log_le_log hN
    (show ((n+1:ℕ):ℝ) ≤ (n:ℝ)^2 by push_cast; nlinarith)
  simpa only [Real.log_pow,Nat.cast_ofNat] using H

theorem observed_critical_power_succ {n : ℕ} (hn : 1 ≤ n)
    {q : ℝ} (hq : -1 ≤ q) :
    (n:ℝ)^q ≤ 2*((n+1:ℕ):ℝ)^q := by
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hN0 : 0 < ((n+1:ℕ):ℝ) := by positivity
  by_cases hq0 : 0 ≤ q
  · have H := Real.rpow_le_rpow hn0.le
      (show (n:ℝ) ≤ ((n+1:ℕ):ℝ) by push_cast; linarith) hq0
    nlinarith [Real.rpow_pos_of_pos hN0 q]
  · have H := Real.rpow_le_rpow_of_nonpos hN0
      (show ((n+1:ℕ):ℝ) ≤ 2*(n:ℝ) by push_cast; linarith) (le_of_not_ge hq0)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hn0.le] at H
    have H2 : (1/2:ℝ) ≤ (2:ℝ)^q := by
      have HH := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hq
      norm_num only [Real.rpow_neg_one] at HH
      exact HH
    have HH := mul_le_mul_of_nonneg_right H2 (Real.rpow_nonneg hn0.le q)
    nlinarith

theorem observed_direct_test_innovation_strength
    {n : ℕ} (hn : 2 ≤ n) {d lam x C v : ℝ}
    (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2) (hx : 0 < x)
    (hC : 1 ≤ C) (hcompare : x^2 ≤ C^2*laplaceComparisonStrength d lam x)
    (hWv : max x (Real.sqrt (laplaceComparisonStrength d lam x)) ≤ v)
    (hv1 : v ≤ 1) :
    let W := max x (Real.sqrt (laplaceComparisonStrength d lam x))
    (1/(24*C^3))*W^3/Real.log (n:ℝ) ≤
      laplaceComparisonStrength d lam v*v/(12*Real.log ((n+1:ℕ):ℝ)) := by
  dsimp only
  let W := max x (Real.sqrt (laplaceComparisonStrength d lam x))
  have hCp : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨hW,_,hstrength⟩ := actual_direct_test_calibration_strength hd hlam hld hx hC hcompare
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log ((n+1:ℕ):ℝ) := Real.log_pos (by push_cast; linarith)
  have hmono := (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).2
  have HG := hmono ⟨hW.le,hWv.trans hv1⟩ ⟨hW.le.trans hWv,hv1⟩ hWv
  have Hmul := mul_le_mul_of_nonneg_right hstrength hW.le
  have Hstrength : (1/C^3)*W^3 ≤ laplaceComparisonStrength d lam v*v := by
    nlinarith only [Hmul,HG]
  have Hlog := observed_log_succ_le_twice hn
  calc
    _ = ((1/C^3)*W^3)/(24*Real.log (n:ℝ)) := by dsimp [W]; ring
    _ ≤ ((1/C^3)*W^3)/(12*Real.log ((n+1:ℕ):ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ ≤ _ := div_le_div_of_nonneg_right Hstrength (by positivity)

theorem native_minimum_observed_calibration_scales
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock C v : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hn : 2 ≤ n) (hm : 0 ≤ m) (hC0 : 0 < C0) (hC : 1 ≤ C)
    (hcompare : a.xs^2 ≤ C^2*laplaceComparisonStrength a.context.d a.lam a.xs)
    (hWv : max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs)) ≤ v)
    (hv1 : v ≤ 1) :
    let W := max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))
    (n:ℝ)^(-(1:ℝ)/6+m) ≤ (2*C0)*a.xs ∧
      (1/(24*C^3))*W^3/Real.log (n:ℝ) ≤
        laplaceComparisonStrength a.context.d a.lam v*v/(12*Real.log ((n+1:ℕ):ℝ)) := by
  dsimp only
  constructor
  · have H := observed_critical_power_succ (by omega : 1 ≤ n)
      (show -1 ≤ -(1:ℝ)/6+m by linarith)
    have Hmin := native_minimum_original_boundary_critical_radius hC0 a
    nlinarith
  · exact observed_direct_test_innovation_strength hn a.context.hd a.hlam a.hld a.hxs
      hC hcompare hWv hv1

end OAI.SKFluctuations.Cavity
