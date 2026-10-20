module

public import ComparisonSignedCavitySecondLowPairSeedObservedZero
public import ComparisonSignedCavityFreshGraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}
set_option maxHeartbeats 30000000

theorem native_second_low_two_blocks_preserved_by_high_mark
    (U : ℕ) (a z : T.Slot)
    (hcover : ∀ v : T.Slot, U ≤ T.splitIndex a v ∨ U ≤ T.splitIndex z v)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (hmark : U ≤ p.tree.splitIndex (p.embed a) p.mark ∨
      U ≤ p.tree.splitIndex (p.embed z) p.mark) :
    ∀ v : p.tree.Slot, U ≤ p.tree.splitIndex (p.embed a) v ∨
      U ≤ p.tree.splitIndex (p.embed z) v := by
  intro v
  rcases markedAttach_slot_coverage T 0 p hp v with rfl | ⟨c,rfl⟩
  · exact hmark
  · simpa only [(T.markedAttach_embed_preserves 0 p hp).2] using hcover c

theorem native_second_low_one_block_marked_two_block_cover
    (U : ℕ) (hU : U ≤ as.length) (a : T.Slot)
    (hcover : ∀ v : T.Slot, U ≤ T.splitIndex a v)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0) :
    ∀ v : p.tree.Slot, U ≤ p.tree.splitIndex (p.embed a) v ∨ U ≤ p.tree.splitIndex p.mark v := by
  intro v
  rcases markedAttach_slot_coverage T 0 p hp v with rfl | ⟨c,rfl⟩
  · exact Or.inr (by rw [p.tree.splitIndex_self];exact hU)
  · exact Or.inl (by rw [(T.markedAttach_embed_preserves 0 p hp).2];exact hcover c)

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000

theorem native_second_low_one_block_marked_observed_class_zero
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (hU : U ≤ as.length)
    (a : T.Slot) (hcover : ∀ v : T.Slot, U ≤ T.splitIndex a v)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (P : p.tree.cavityLeft.Assignment → ℝ) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K p.tree hU P (p.embed a) p.mark j true = 0 :=
  native_second_low_observed_class_zero_of_two_old_blocks n q U b h K p.tree hU P (p.embed a) p.mark
    (native_second_low_one_block_marked_two_block_cover U hU a hcover p hp) j

theorem native_second_low_single_fresh_graft_observed_class_zero
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    (as : List PositiveMass) (hU : U ≤ as.length) (star : ℕ)
    (P : (nativeFreshAtSlot (single (S:=Spin n × Bool) as) 0 (singleSlot as) star).tree.cavityLeft.Assignment → ℝ)
    (j : Fin 8) :
    let g := nativeFreshAtSlot (single (S:=Spin n × Bool) as) 0 (singleSlot as) star
    nativeSecondLowClassLedger n q U b h K g.tree hU P (g.embed (singleSlot as)) g.mark j true = 0 := by
  apply native_second_low_one_block_marked_observed_class_zero n q U b h K (single as) hU
    (singleSlot as) _ _ (nativeFreshAtSlot_mem (single as) 0 (singleSlot as) star) P j
  intro v
  rw [native_second_low_single_slot_unique as v,splitIndex_self]
  exact hU

theorem native_second_low_constant_single_fresh_graft_observed_class_zero
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    (as : List PositiveMass) (hU : U ≤ as.length) (star : ℕ) (j : Fin 8) :
    let g := nativeFreshAtSlot (single (S:=Spin n × Bool) as) 0 (singleSlot as) star
    nativeSecondLowClassLedger n q U b h K g.tree hU (fun _ => 1) (g.embed (singleSlot as)) g.mark j true = 0 :=
  native_second_low_single_fresh_graft_observed_class_zero n q U b h K as hU star (fun _ => 1) j

end OAI.SKFluctuations.Cavity
