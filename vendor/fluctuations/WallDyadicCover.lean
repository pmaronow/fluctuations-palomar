module

public import Mathlib

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.WallSweep

open MeasureTheory Set
open scoped BigOperators

def wallDyadicCut (s : ℝ) (k : ℕ) : ℝ := s - s / (2 : ℝ) ^ (k + 1)

theorem wallDyadicCut_zero (s : ℝ) : wallDyadicCut s 0 = s / 2 := by
  simp [wallDyadicCut]
  ring

theorem wallDyadicCut_one (s : ℝ) : wallDyadicCut s 1 = 3 * s / 4 := by
  norm_num [wallDyadicCut]
  ring

theorem wallDyadicCut_le {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    wallDyadicCut s k ≤ s := by
  unfold wallDyadicCut
  have : 0 ≤ s / (2 : ℝ) ^ (k + 1) := by positivity
  linarith

theorem wallDyadicCut_monotone {s : ℝ} (hs : 0 ≤ s) :
    Monotone (wallDyadicCut s) := by
  apply monotone_nat_of_le_succ
  intro k
  unfold wallDyadicCut
  have hp : 0 < (2 : ℝ) ^ (k + 1) := by positivity
  apply sub_le_sub_left
  exact div_le_div_of_nonneg_left hs hp
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : k + 1 ≤ k + 1 + 1))

theorem adjacent_band_cost {B : ℝ → ℝ} (cuts : ℕ → ℝ) (K : ℕ)
    {C E : ℝ}
    (hint : ∀ k < K, IntervalIntegrable B volume (cuts k) (cuts (k + 1)))
    (hband : ∀ k < K, (∫ u in cuts k..cuts (k + 1), B u) ≤
      C * (cuts (k + 1) - cuts k) + E) :
    (∫ u in cuts 0..cuts K, B u) ≤ C * (cuts K - cuts 0) + (K : ℝ) * E := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  calc
    _ ≤ ∑ k ∈ Finset.range K, (C * (cuts (k + 1) - cuts k) + E) := by
      exact Finset.sum_le_sum fun k hk => hband k (Finset.mem_range.mp hk)
    _ = C * (cuts K - cuts 0) + (K : ℝ) * E := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub]
      simp

theorem monotone_initial_half_cost {s : ℝ} (hs : 0 ≤ s) {B : ℝ → ℝ}
    (hB : Monotone B) :
    (∫ u in 0..s / 2, B u) ≤ 2 * (∫ u in s / 2..3 * s / 4, B u) := by
  have hleft := intervalIntegral.integral_mono_on
    (show (0 : ℝ) ≤ s / 2 by positivity) (hB.intervalIntegrable (μ := volume))
    (intervalIntegrable_const (μ := volume) (c := B (s / 2)))
    (fun u hu => hB hu.2)
  have hright := intervalIntegral.integral_mono_on
    (show s / 2 ≤ 3 * s / 4 by linarith)
    (intervalIntegrable_const (μ := volume) (c := B (s / 2)))
    (hB.intervalIntegrable (μ := volume)) (fun u hu => hB hu.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hleft hright
  nlinarith

theorem full_low_mass_cost {s : ℝ} (hs : 0 ≤ s) {B : ℝ → ℝ}
    (hB : Monotone B) (hB0 : ∀ u ∈ Icc 0 s, 0 ≤ B u)
    (hB1 : ∀ u ∈ Icc 0 s, B u ≤ 1) (K : ℕ) (hK : 1 ≤ K)
    {C E : ℝ} (hC : 0 ≤ C)
    (hband : ∀ k < K,
      (∫ u in wallDyadicCut s k..wallDyadicCut s (k + 1), B u) ≤
        C * (wallDyadicCut s (k + 1) - wallDyadicCut s k) + E) :
    (∫ u in 0..s, B u) ≤
      3 * (C * (s / 2) + (K : ℝ) * E) + s / (2 : ℝ) ^ (K + 1) := by
  have hmono := wallDyadicCut_monotone hs
  have ha0 : wallDyadicCut s 0 = s / 2 := wallDyadicCut_zero s
  have ha1 : wallDyadicCut s 1 = 3 * s / 4 := wallDyadicCut_one s
  have hhalf : s / 2 ≤ wallDyadicCut s K := by
    rw [← ha0]
    exact hmono (Nat.zero_le K)
  have hthree : 3 * s / 4 ≤ wallDyadicCut s K := by
    rw [← ha1]
    exact hmono hK
  have hlast := wallDyadicCut_le hs K
  have hsum := adjacent_band_cost (B := B) (wallDyadicCut s) K
    (fun _ _ => hB.intervalIntegrable) hband
  rw [ha0] at hsum
  have hsum' : (∫ u in s / 2..wallDyadicCut s K, B u) ≤
      C * (s / 2) + (K : ℝ) * E := by
    have hc := mul_le_mul_of_nonneg_left (show wallDyadicCut s K - s / 2 ≤ s / 2 by
      linarith) hC
    linarith
  have hrest0 : 0 ≤ (∫ u in 3 * s / 4..wallDyadicCut s K, B u) := by
    apply intervalIntegral.integral_nonneg hthree
    intro u hu
    apply hB0 u
    constructor <;> linarith [hu.1, hu.2]
  have hfirst : (∫ u in s / 2..3 * s / 4, B u) ≤
      (∫ u in s / 2..wallDyadicCut s K, B u) := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (a := s / 2) (b := 3 * s / 4) (c := wallDyadicCut s K)
      (hB.intervalIntegrable (μ := volume)) (hB.intervalIntegrable (μ := volume))
    linarith
  have hprefix := (monotone_initial_half_cost hs hB).trans
    (mul_le_mul_of_nonneg_left hfirst (by norm_num : (0 : ℝ) ≤ 2))
  have hterminal : (∫ u in wallDyadicCut s K..s, B u) ≤ s - wallDyadicCut s K := by
    have h := intervalIntegral.integral_mono_on hlast (hB.intervalIntegrable (μ := volume))
      (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) (fun u hu => hB1 u
        ⟨by linarith [hu.1], hu.2⟩)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using h
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := s / 2) (c := wallDyadicCut s K)
    (hB.intervalIntegrable (μ := volume)) (hB.intervalIntegrable (μ := volume))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := wallDyadicCut s K) (c := s)
    (hB.intervalIntegrable (μ := volume)) (hB.intervalIntegrable (μ := volume))
  have hres : s - wallDyadicCut s K = s / (2 : ℝ) ^ (K + 1) := by
    unfold wallDyadicCut
    ring
  rw [hres] at hterminal
  linarith

end OAI.SKFluctuations.WallSweep
