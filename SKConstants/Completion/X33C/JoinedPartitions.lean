module

public import SKConstants.Completion.X33C.OriginalPartitions

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X33C
open SKConstantsOAI.ZeroTemperatureSK S71.Mesh
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance joined_W_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance joined_Z_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

def joinedDyadicTime (S T : ℝ≥0) (l k : ℕ) : ℝ≥0 :=
  if k ≤ 2 ^ l then (brownianDyadicGrid S).time l k
    else S + (brownianDyadicGrid T).time l (k - 2 ^ l)

theorem joinedDyadicTime_pre (S T : ℝ≥0) (l k : ℕ) (hk : k ≤ 2 ^ l) :
    joinedDyadicTime S T l k = (brownianDyadicGrid S).time l k := by
  simp only [joinedDyadicTime, ite_eq_left hk]

theorem joinedDyadicTime_post (S T : ℝ≥0) (l k : ℕ) :
    joinedDyadicTime S T l (2 ^ l + k) = S + (brownianDyadicGrid T).time l k := by
  by_cases hk : k = 0
  · subst k
    simp [joinedDyadicTime, brownianDyadicGrid]
  · simp only [joinedDyadicTime, ite_eq_right (show ¬2 ^ l + k ≤ 2 ^ l by omega), Nat.add_sub_cancel_left]

theorem joinedDyadicTime_monotone (S T : ℝ≥0) (l : ℕ) : Monotone (joinedDyadicTime S T l) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k < 2 ^ l
  · rw [joinedDyadicTime_pre S T l k hk.le, joinedDyadicTime_pre S T l (k + 1) hk]
    exact (brownianDyadicGrid S).monotone l (Nat.le_succ k)
  · obtain hk | hk := eq_or_lt_of_le (le_of_not_gt hk)
    · subst k
      rw [joinedDyadicTime_pre S T l (2 ^ l) le_rfl, joinedDyadicTime_post S T l 1]
      simp [brownianDyadicGrid]
    · rw [show k = 2 ^ l + (k - 2 ^ l) by omega, joinedDyadicTime_post,
        show 2 ^ l + (k - 2 ^ l) + 1 = 2 ^ l + (k - 2 ^ l + 1) by omega,
        joinedDyadicTime_post]
      exact add_le_add le_rfl ((brownianDyadicGrid T).monotone l (Nat.le_succ _))

theorem joinedDyadicTime_zero (S T : ℝ≥0) (l : ℕ) : joinedDyadicTime S T l 0 = 0 := by
  rw [joinedDyadicTime_pre S T l 0 (Nat.zero_le _)]
  exact (brownianDyadicGrid S).zero l

theorem joinedDyadicTime_end (S T : ℝ≥0) (l : ℕ) :
    joinedDyadicTime S T l (2 ^ l + 2 ^ l) = S + T := by
  rw [joinedDyadicTime_post]
  simp [brownianDyadicGrid]

theorem joinedDyadicTime_width (S T : ℝ≥0) (l k : ℕ) :
    (joinedDyadicTime S T l (k + 1) : ℝ) - joinedDyadicTime S T l k ≤
      brownianDyadicWidth S l + brownianDyadicWidth T l := by
  have hS : 0 ≤ brownianDyadicWidth S l := by unfold brownianDyadicWidth; positivity
  have hT : 0 ≤ brownianDyadicWidth T l := by unfold brownianDyadicWidth; positivity
  by_cases hk : k < 2 ^ l
  · rw [joinedDyadicTime_pre S T l k hk.le, joinedDyadicTime_pre S T l (k + 1) hk]
    exact (brownianDyadicGrid_width_le S l k).trans (le_add_of_nonneg_right hT)
  · have hk' : 2 ^ l ≤ k := le_of_not_gt hk
    have he : k = 2 ^ l + (k - 2 ^ l) := by omega
    rw [he, joinedDyadicTime_post,
      show 2 ^ l + (k - 2 ^ l) + 1 = 2 ^ l + (k - 2 ^ l + 1) by omega,
      joinedDyadicTime_post]
    simp only [NNReal.coe_add, add_sub_add_left_eq_sub]
    exact (brownianDyadicGrid_width_le T l _).trans (le_add_of_nonneg_left hS)

theorem joinedPartitionSum_split (H B : ℝ≥0 → ℝ) (S T : ℝ≥0) (l : ℕ) :
    partitionSum H B (joinedDyadicTime S T l) (2 ^ l + 2 ^ l) =
      partitionSum H B ((brownianDyadicGrid S).time l) (2 ^ l) +
        partitionSum H B (fun k => S + (brownianDyadicGrid T).time l k) (2 ^ l) := by
  unfold partitionSum
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [joinedDyadicTime_pre S T l k (Finset.mem_range.mp hk).le,
      joinedDyadicTime_pre S T l (k + 1) (Finset.mem_range.mp hk)]
  · apply Finset.sum_congr rfl
    intro k _
    rw [joinedDyadicTime_post, show 2 ^ l + k + 1 = 2 ^ l + (k + 1) by omega,
      joinedDyadicTime_post]

theorem joinedOriginalSum_comparison_tendsto
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (S T : ℝ≥0) :
    Tendsto (fun l => ∫ u : (Bool × Ω) × A,
      (originalPartitionSum W β (joinedDyadicTime S T l) (2 ^ l + 2 ^ l) u -
        S33aA.originalRowLeftSum W β (S + T) l u) ^ 2 ∂LM4.actualRowBaseLaw W Z)
      atTop (𝓝 0) := by
  exact originalPartitionSum_comparison_tendsto W Z β (S + T)
    (joinedDyadicTime S T) ((brownianDyadicGrid (S + T)).time)
    (fun l => 2 ^ l + 2 ^ l) (fun l => 2 ^ l)
    (joinedDyadicTime_monotone S T) (brownianDyadicGrid (S + T)).monotone (fun _ => by positivity)
    (joinedDyadicTime_zero S T) (brownianDyadicGrid (S + T)).zero
    (joinedDyadicTime_end S T) (fun l => by simp [brownianDyadicGrid])
    (fun l => brownianDyadicWidth S l + brownianDyadicWidth T l)
    (brownianDyadicWidth (S + T))
    (by simpa using (brownianDyadicWidth_tendsto S).add (brownianDyadicWidth_tendsto T))
    (brownianDyadicWidth_tendsto (S + T))
    (fun l k _ => joinedDyadicTime_width S T l k)
    (fun l k _ => brownianDyadicGrid_width_le (S + T) l k)

end SKConstants.Completion.X33C
