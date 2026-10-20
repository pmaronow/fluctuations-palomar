module

public import ComparisonSignedCavitySecondLowUnobservedEntry
public import ComparisonSignedCavitySecondLowObservedPartition
public import ComparisonSignedCavityForestObservedHighGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 22000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowFirstMiddleIsFirst (j : Fin 8) : Bool :=
  match j.val with
  | 2|3|4|6=>true
  | _=>false

theorem nativeSecondLowPathMiddle_map {α β : Type*} (F : α→β) (j : Fin 8)
    (f c e d : α) :
    F (nativeSecondLowPathMiddle j f c e d)=nativeSecondLowPathMiddle j (F f) (F c) (F e) (F d) := by
  fin_cases j <;> rfl

theorem native_second_low_path_middle_eq_first_entry {α : Type*} (A B f c e d : α)
    (j : Fin 8) (H : nativeSecondLowBlockPath j A B f c e d) :
    nativeSecondLowPathMiddle j f c e d=
      if nativeSecondLowFirstMiddleIsFirst j then f else c := by
  fin_cases j
  all_goals dsimp only [nativeSecondLowPathMiddle,nativeSecondLowFirstMiddleIsFirst,
    nativeSecondLowBlockPath] at H ⊢
  all_goals first | rfl | exact H.2.1

theorem native_second_low_word_observed_first_entry_iff {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (hU : U≤as.length) (a z : T.Slot)
    (p : MarkedPlacement T) (_hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (j : Fin 8) (H : nativeSecondLowWordPath U hU a z p r s t j) :
    nativeSecondLowWordObserved U p r s t j ↔
      if nativeSecondLowFirstMiddleIsFirst j then
        ∃v:T.Slot,U≤p.tree.splitIndex (p.embed v) p.mark
      else ∃v:T.Slot,U≤r.tree.splitIndex (r.embed (p.embed v)) r.mark := by
  let B:=t.tree.cutBlock U hU
  have Hmid : B (nativeSecondLowWordMiddle p r s t j)=
      if nativeSecondLowFirstMiddleIsFirst j then B (t.embed (s.embed (r.embed p.mark)))
        else B (t.embed (s.embed r.mark)) := by
    rw [nativeSecondLowWordMiddle,nativeSecondLowPathMiddle_map B j _ _ _ _]
    exact native_second_low_path_middle_eq_first_entry _ _ _ _ _ _ j H
  unfold nativeSecondLowWordObserved
  have Hblock (v : T.Slot) :
      U≤t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed v))))
          (nativeSecondLowWordMiddle p r s t j) ↔
      if nativeSecondLowFirstMiddleIsFirst j then U≤p.tree.splitIndex (p.embed v) p.mark
        else U≤r.tree.splitIndex (r.embed (p.embed v)) r.mark := by
    rw [←t.tree.cutBlock_eq_iff U hU]
    change B (t.embed (s.embed (r.embed (p.embed v))))=B (nativeSecondLowWordMiddle p r s t j) ↔ _
    rw [Hmid]
    cases HF : nativeSecondLowFirstMiddleIsFirst j
    · simp only [Bool.false_eq_true,↓reduceIte]
      rw [t.tree.cutBlock_eq_iff U hU,
        (s.tree.markedAttach_embed_preserves 0 t ht).2,
        (r.tree.markedAttach_embed_preserves 0 s hs).2]
    · simp only [↓reduceIte]
      rw [t.tree.cutBlock_eq_iff U hU,
        (s.tree.markedAttach_embed_preserves 0 t ht).2,
        (r.tree.markedAttach_embed_preserves 0 s hs).2,
        (p.tree.markedAttach_embed_preserves 0 r hr).2]
  cases HF : nativeSecondLowFirstMiddleIsFirst j <;>
    simp only [HF,Bool.false_eq_true,↓reduceIte] at Hblock ⊢
  all_goals exact exists_congr Hblock

theorem native_second_low_unobserved_source_entry {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (hU : U≤as.length) (a z : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (j : Fin 8) (H : nativeSecondLowWordPath U hU a z p r s t j)
    (Hunobserved : ¬nativeSecondLowWordObserved U p r s t j)
    (Hlow : r.tree.splitIndex (r.embed p.mark) r.mark<U) :
    if nativeSecondLowFirstMiddleIsFirst j then p∈nativeSecondLowUnobservedEntryRows T U 0
      else r∈nativeSecondLowUnobservedEntryRows p.tree U 0 := by
  have HH:=native_second_low_word_observed_first_entry_iff T U hU a z p hp r hr s hs t ht j H
  cases HF : nativeSecondLowFirstMiddleIsFirst j
  · simp only [HF,Bool.false_eq_true,↓reduceIte] at HH ⊢
    rw [mem_nativeSecondLowUnobservedEntryRows]
    refine ⟨hr,?_⟩
    rintro ⟨v,Hv⟩
    rcases markedAttach_slot_coverage T 0 p hp v with rfl|⟨w,rfl⟩
    · omega
    · exact Hunobserved (HH.mpr ⟨w,Hv⟩)
  · simp only [HF,↓reduceIte] at HH ⊢
    rw [mem_nativeSecondLowUnobservedEntryRows]
    exact ⟨hp,fun HV=>Hunobserved (HH.mpr HV)⟩

end OAI.SKFluctuations.Cavity
