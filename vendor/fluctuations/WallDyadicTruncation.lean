module

public import WallDyadicCover
public import UpperWallIteration

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.WallSweep

open MeasureTheory Set
open PositiveLaplaceAssembly

def wallDyadicCount (s tau : ℝ) : ℕ := logarithmicCount 2 (s / tau) + 1

theorem wallDyadicCount_pos (s tau : ℝ) : 1 ≤ wallDyadicCount s tau := by
  unfold wallDyadicCount
  omega

theorem wallDyadicCount_residual_le {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) :
    s / (2 : ℝ) ^ (wallDyadicCount s tau + 1) ≤ tau := by
  have hp := pow_logarithmicCount_ge (by norm_num : (1 : ℝ) < 2) (div_pos hs htau)
  have hpow : (2 : ℝ) ^ logarithmicCount 2 (s / tau) ≤
      (2 : ℝ) ^ (wallDyadicCount s tau + 1) := by
    apply pow_le_pow_right₀ (by norm_num)
    unfold wallDyadicCount
    omega
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (wallDyadicCount s tau + 1))).mpr
  have h := (div_le_iff₀ htau).mp (hp.trans hpow)
  nlinarith

theorem wallDyadicCount_le_log {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {n : ℕ} (hn : 1 < (n : ℝ)) (hnlog : 1 ≤ Real.log (n : ℝ)) :
    (wallDyadicCount s ((n : ℝ) ^ (-10 : ℝ)) : ℝ) ≤
      (10 / Real.log 2 + 2) * Real.log (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hn
  have htau : 0 < (n : ℝ) ^ (-10 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hr : s / (n : ℝ) ^ (-10 : ℝ) ≤ (n : ℝ) ^ (10 : ℝ) := by
    rw [Real.rpow_neg hn0.le, div_inv_eq_mul]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) hs1
  have hlog := Real.log_le_log (div_pos hs htau) hr
  rw [Real.log_rpow hn0] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := (div_le_div_of_nonneg_right hlog hlog2.le)
  have hdiv' : Real.log (s / (n : ℝ) ^ (-10 : ℝ)) / Real.log 2 ≤
      10 / Real.log 2 * Real.log (n : ℝ) := by
    convert hdiv using 1 <;> ring
  have hcount : (logarithmicCount 2 (s / (n : ℝ) ^ (-10 : ℝ)) : ℝ) ≤
      10 / Real.log 2 * Real.log (n : ℝ) + 1 := by
    unfold logarithmicCount
    by_cases hnonneg : 0 ≤ Real.log (s / (n : ℝ) ^ (-10 : ℝ)) / Real.log 2
    · have hc := (Nat.ceil_lt_add_one hnonneg).le
      linarith
    · rw [Nat.ceil_eq_zero.mpr (le_of_not_ge hnonneg)]
      simp only [Nat.cast_zero]
      positivity
  unfold wallDyadicCount
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem full_low_mass_cost_logarithmic {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {B : ℝ → ℝ} (hB : Monotone B) (hB0 : ∀ u ∈ Icc 0 s, 0 ≤ B u)
    (hB1 : ∀ u ∈ Icc 0 s, B u ≤ 1) {n : ℕ}
    (hn : 1 < (n : ℝ)) (hnlog : 1 ≤ Real.log (n : ℝ))
    {C E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hband : ∀ k < wallDyadicCount s ((n : ℝ) ^ (-10 : ℝ)),
      (∫ u in wallDyadicCut s k..wallDyadicCut s (k + 1), B u) ≤
        C * (wallDyadicCut s (k + 1) - wallDyadicCut s k) + E) :
    (∫ u in 0..s, B u) ≤ 3 * C * (s / 2) +
      3 * (10 / Real.log 2 + 2) * Real.log (n : ℝ) * E + (n : ℝ) ^ (-10 : ℝ) := by
  have h := full_low_mass_cost hs.le hB hB0 hB1
    (wallDyadicCount s ((n : ℝ) ^ (-10 : ℝ))) (wallDyadicCount_pos _ _) hC hband
  have hr := wallDyadicCount_residual_le hs
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hn) (-10 : ℝ))
  have hc := mul_le_mul_of_nonneg_right (wallDyadicCount_le_log hs hs1 hn hnlog) hE
  nlinarith

end OAI.SKFluctuations.WallSweep
