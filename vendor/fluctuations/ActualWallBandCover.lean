module

public import SKFluctuationsOAI.Probability.SKFluctuations.ClockRetainTwo
public import SKFluctuationsOAI.Probability.SKFluctuations.InverseConstraintNonempty
public import WallDyadicTruncation

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem orderedPathB_zero (n : ℕ) (b h : ℝ → ℝ≥0) : orderedPathB n b h 0 = 0 := by
  simp [orderedPathB, orderedPathPair, pathPairMoment]

theorem orderedPathB_nonneg_Icc (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : 0 ≤ orderedPathB n b h u := by
  by_cases hzero : u = 0
  · rw [hzero, orderedPathB_zero]
  · have hp : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hzero)
    have hbounds := orderedPath_SK_bounds n hn b h hb hh ⟨hp, hu.2⟩
    exact (sq_nonneg (orderedPathS n b h u)).trans hbounds.2.2.1

theorem orderedPathB_le_one_Icc (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : orderedPathB n b h u ≤ 1 := by
  by_cases hzero : u = 0
  · rw [hzero, orderedPathB_zero]
    norm_num
  · exact (orderedPath_SK_bounds n hn b h hb hh
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero), hu.2⟩).2.2.2

theorem orderedPathB_monotone_Icc (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    MonotoneOn (orderedPathB n b h) (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  by_cases hzero : u = 0
  · rw [hzero, orderedPathB_zero]
    exact orderedPathB_nonneg_Icc n hn b h hb hh hv
  · have hp : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hzero)
    exact (orderedPath_SK_monotone n hn b h hb hh).2 ⟨hp, hu.2⟩
      ⟨hp.trans_le huv, hv.2⟩ huv

def clippedOrderedPathB (n : ℕ) (b h : ℝ → ℝ≥0) (u : ℝ) : ℝ :=
  orderedPathB n b h (min (max u 0) 1)

theorem clippedOrderedPathB_eq (n : ℕ) (b h : ℝ → ℝ≥0)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    clippedOrderedPathB n b h u = orderedPathB n b h u := by
  simp only [clippedOrderedPathB, max_eq_left hu.1, min_eq_left hu.2]

theorem clippedOrderedPathB_monotone (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    Monotone (clippedOrderedPathB n b h) := by
  intro u v huv
  have hmem (x : ℝ) : min (max x 0) 1 ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  exact orderedPathB_monotone_Icc n hn b h hb hh (hmem u) (hmem v)
    (min_le_min (max_le_max huv le_rfl) le_rfl)

theorem orderedPathB_full_low_mass_cost {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (n : ℕ) (hn : 1 < (n : ℝ)) (hnlog : 1 ≤ Real.log (n : ℝ))
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1)) {C E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hband : ∀ k < WallSweep.wallDyadicCount s ((n : ℝ) ^ (-10 : ℝ)),
      (∫ u in WallSweep.wallDyadicCut s k..WallSweep.wallDyadicCut s (k + 1), orderedPathB n b h u) ≤
        C * (WallSweep.wallDyadicCut s (k + 1) - WallSweep.wallDyadicCut s k) + E) :
    (∫ u in 0..s, orderedPathB n b h u) ≤ 3 * C * (s / 2) +
      3 * (10 / Real.log 2 + 2) * Real.log (n : ℝ) * E + (n : ℝ) ^ (-10 : ℝ) := by
  have hn0 : 0 < n := by exact_mod_cast lt_trans zero_lt_one hn
  have hsame {a z : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1) :
      (∫ u in a..z, clippedOrderedPathB n b h u) = (∫ u in a..z, orderedPathB n b h u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le haz] at hu
    exact clippedOrderedPathB_eq n b h ⟨ha.trans hu.1, hu.2.trans hz⟩
  have hclipped := WallSweep.full_low_mass_cost_logarithmic hs hs1
    (clippedOrderedPathB_monotone n hn0 b h hb hh)
    (fun u hu => by
      rw [clippedOrderedPathB_eq n b h ⟨hu.1, hu.2.trans hs1⟩]
      exact orderedPathB_nonneg_Icc n hn0 b h hb hh ⟨hu.1, hu.2.trans hs1⟩)
    (fun u hu => by
      rw [clippedOrderedPathB_eq n b h ⟨hu.1, hu.2.trans hs1⟩]
      exact orderedPathB_le_one_Icc n hn0 b h hb hh ⟨hu.1, hu.2.trans hs1⟩)
    hn hnlog hC hE (fun k hk => by
      have hmono := WallSweep.wallDyadicCut_monotone hs.le
      have hl := hmono (Nat.zero_le k)
      rw [WallSweep.wallDyadicCut_zero] at hl
      rw [hsame (by linarith) (hmono (Nat.le_succ k))
        ((WallSweep.wallDyadicCut_le hs.le (k + 1)).trans hs1)]
      exact hband k hk)
  rw [hsame (by norm_num) hs.le hs1] at hclipped
  exact hclipped

end OAI.SKFluctuations.LaplaceWindowFormalization
