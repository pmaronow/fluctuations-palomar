module

public import ComparisonSignedCavitySecondLowTwoBlockObservedZero

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}
set_option maxHeartbeats 30000000

theorem native_second_low_single_slot_unique (as : List PositiveMass)
    (v : (single (S:=S) as).Slot) : v = singleSlot as := by
  induction as with
  | nil => cases v; rfl
  | cons a as ih => exact ih v

theorem native_second_low_pair_seed_slot_cases (as : List PositiveMass) (i : ℕ)
    (v : (pairClock (S:=S) as i).Slot) :
    v = pairLeftSlot as i ∨ v = pairRightSlot as i := by
  induction as generalizing i with
  | nil =>
    cases v with
    | inl v => exact Or.inl (congrArg Sum.inl (Subsingleton.elim _ _))
    | inr v => exact Or.inr (congrArg Sum.inr (Subsingleton.elim _ _))
  | cons a as ih =>
    cases i with
    | zero =>
      cases v with
      | inl v => exact Or.inl (congrArg Sum.inl (native_second_low_single_slot_unique (a::as) v))
      | inr v => exact Or.inr (congrArg Sum.inr (native_second_low_single_slot_unique (a::as) v))
    | succ i => exact ih i v

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000

theorem native_second_low_pair_seed_observed_class_zero
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    (as : List PositiveMass) (hU : U ≤ as.length) (i : ℕ)
    (P : (pairClock (S:=Spin n × Bool) as i).cavityLeft.Assignment → ℝ) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K (pairClock as i) hU P
      (pairLeftSlot as i) (pairRightSlot as i) j true = 0 := by
  apply native_second_low_observed_class_zero_of_two_old_blocks
  intro v
  rcases native_second_low_pair_seed_slot_cases as i v with rfl | rfl
  · exact Or.inl (by rw [splitIndex_self];exact hU)
  · exact Or.inr (by rw [splitIndex_self];exact hU)

theorem native_second_low_constant_pair_seed_observed_class_zero
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    (as : List PositiveMass) (hU : U ≤ as.length) (i : ℕ) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K (pairClock as i) hU (fun _ => 1)
      (pairLeftSlot as i) (pairRightSlot as i) j true = 0 :=
  native_second_low_pair_seed_observed_class_zero n q U b h K as hU i (fun _ => 1) j

end OAI.SKFluctuations.Cavity
