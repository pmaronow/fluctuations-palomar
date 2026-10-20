module

public import ComparisonSignedCavitySecondLowObservedPartition
public import ComparisonSignedCavitySecondLowEightLabeledRouting

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped BigOperators
variable {S : Type} {as : List PositiveMass} {T V : ClockTree S as}
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

@[instance_reducible] def nativeSecondLowSlotFintype : {as : List PositiveMass} → (T : ClockTree S as) → Fintype T.Slot
  | _, .leaf => inferInstanceAs (Fintype Unit)
  | _, .step _ T => nativeSecondLowSlotFintype T
  | _, .fork T V => by
    letI := nativeSecondLowSlotFintype T
    letI := nativeSecondLowSlotFintype V
    exact inferInstanceAs (Fintype (T.Slot ⊕ V.Slot))

@[instance_reducible] def nativeSecondLowOccupiedBlockFintype (T : ClockTree S as) (U : ℕ)
    (hU : U ≤ as.length) : Fintype (T.CutBlock U hU) := by
  letI := nativeSecondLowSlotFintype T
  exact Fintype.ofSurjective (T.cutBlock U hU) (fun B => ⟨Quotient.out B,Quotient.out_eq B⟩)

attribute [instance] nativeSecondLowOccupiedBlockFintype

def nativeSecondLowOccupiedBlockRepresentative (T : ClockTree S as) (U : ℕ)
    (hU : U ≤ as.length) (B : T.CutBlock U hU) : T.Slot := Quotient.out B

theorem native_second_low_occupied_block_representative_eq
    (U : ℕ) (hU : U ≤ as.length) (B : T.CutBlock U hU) :
    T.cutBlock U hU (nativeSecondLowOccupiedBlockRepresentative T U hU B) = B :=
  Quotient.out_eq B

theorem native_second_low_original_occupied_block_unique
    (U : ℕ) (hU : U ≤ as.length) (embed : T.Slot → V.Slot)
    (he : ∀ c d, V.splitIndex (embed c) (embed d) = T.splitIndex c d)
    (m : V.Slot) (B C : T.CutBlock U hU)
    (hB : U ≤ V.splitIndex (embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)) m)
    (hC : U ≤ V.splitIndex (embed (nativeSecondLowOccupiedBlockRepresentative T U hU C)) m) :
    B = C := by
  have HC : U ≤ V.splitIndex m (embed (nativeSecondLowOccupiedBlockRepresentative T U hU C)) := by
    simpa only [V.splitIndex_symm] using hC
  have H := V.splitIndex_cut_trans U _ _ _ hB HC
  rw [he] at H
  have HBC := (T.cutBlock_eq_iff U hU _ _).mpr H
  simpa only [native_second_low_occupied_block_representative_eq] using HBC

theorem native_second_low_original_observed_iff_occupied_block
    (U : ℕ) (hU : U ≤ as.length) (embed : T.Slot → V.Slot)
    (he : ∀ c d, V.splitIndex (embed c) (embed d) = T.splitIndex c d) (m : V.Slot) :
    (∃ c : T.Slot, U ≤ V.splitIndex (embed c) m) ↔
      ∃ B : T.CutBlock U hU,
        U ≤ V.splitIndex (embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)) m := by
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨T.cutBlock U hU c,?_⟩
    have HR : T.cutBlock U hU
        (nativeSecondLowOccupiedBlockRepresentative T U hU (T.cutBlock U hU c)) = T.cutBlock U hU c :=
      native_second_low_occupied_block_representative_eq U hU _
    have HS := (T.cutBlock_eq_iff U hU _ _).mp HR
    have HE : U ≤ V.splitIndex
        (embed (nativeSecondLowOccupiedBlockRepresentative T U hU (T.cutBlock U hU c))) (embed c) := by
      rw [he]
      exact HS
    exact V.splitIndex_cut_trans U _ _ _ HE hc
  · rintro ⟨B,hB⟩
    exact ⟨nativeSecondLowOccupiedBlockRepresentative T U hU B,hB⟩

theorem native_second_low_original_observed_value_eq_occupied_blocks
    (U : ℕ) (hU : U ≤ as.length) (embed : T.Slot → V.Slot)
    (he : ∀ c d, V.splitIndex (embed c) (embed d) = T.splitIndex c d) (m : V.Slot) (Z : ℝ) :
    (if ∃ c : T.Slot, U ≤ V.splitIndex (embed c) m then Z else 0) =
      ∑ B : T.CutBlock U hU,
        if U ≤ V.splitIndex (embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)) m then Z else 0 := by
  classical
  rw [native_second_low_original_observed_iff_occupied_block U hU embed he m]
  by_cases HO : ∃ B : T.CutBlock U hU,
      U ≤ V.splitIndex (embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)) m
  · obtain ⟨B,hB⟩ := HO
    rw [ite_eq_left ⟨B,hB⟩,Finset.sum_eq_single B]
    · simp only [hB,ite_true]
    · intro C _ hCB
      have HC : ¬ U ≤ V.splitIndex (embed (nativeSecondLowOccupiedBlockRepresentative T U hU C)) m := by
        intro HC
        exact hCB (native_second_low_original_occupied_block_unique U hU embed he m C B HC hB)
      simp only [HC,ite_false]
    · simp
  · rw [ite_eq_right HO]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro B _
    have HB : ¬ U ≤ V.splitIndex (embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)) m :=
      fun hB => HO ⟨B,hB⟩
    simp only [HB,ite_false]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_word_observed_value_eq_occupied_blocks
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (U : ℕ) (hU : U ≤ as.length)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) (j : Fin 8) (Z : ℝ) :
    (if nativeSecondLowWordObserved U p r s t j then Z else 0) =
      ∑ B : T.CutBlock U hU,
        if U ≤ t.tree.splitIndex
          (t.embed (s.embed (r.embed (p.embed (nativeSecondLowOccupiedBlockRepresentative T U hU B)))))
          (nativeSecondLowWordMiddle p r s t j) then Z else 0 := by
  unfold nativeSecondLowWordObserved
  apply native_second_low_original_observed_value_eq_occupied_blocks U hU _ _ _ Z
  intro c d
  rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
    (r.tree.markedAttach_embed_preserves 0 s hs).2,
    (p.tree.markedAttach_embed_preserves 0 r hr).2,
    (T.markedAttach_embed_preserves 0 p hp).2]

end OAI.SKFluctuations.Cavity
