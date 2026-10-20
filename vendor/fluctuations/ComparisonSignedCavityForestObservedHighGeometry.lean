module

public import CavityAttachmentCoordinateProjection
public import ComparisonSignedCavityForestTwinClassificationLaw
public import ComparisonSignedCavityForestSameArmClassificationLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem markedAttach_slot_coverage (T : ClockTree S as)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a) (c : p.tree.Slot) :
    c=p.mark ∨ ∃d : T.Slot,c=p.embed d := by
  induction T generalizing a with
  | leaf=>
    rcases List.mem_cons.mp hp with rfl|hp
    · exact Or.inr ⟨c,rfl⟩
    · obtain rfl:=List.mem_singleton.mp hp
      cases c with
      | inl d=>exact Or.inr ⟨d,rfl⟩
      | inr d=>exact Or.inl (congrArg Sum.inr (native_single_slot_eq [] d))
  | @step b tail T ih=>
    rcases List.mem_cons.mp hp with rfl|hp
    · cases c with
      | inl d=>exact Or.inr ⟨d,rfl⟩
      | inr d=>exact Or.inl (congrArg Sum.inr (native_single_slot_eq (b::tail) d))
    · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
      exact ih b.val r hr c
  | @fork tail T V ihT ihV=>
    rcases List.mem_cons.mp hp with rfl|hp
    · cases c with
      | inl d=>exact Or.inr ⟨d,rfl⟩
      | inr d=>exact Or.inl (congrArg Sum.inr (native_single_slot_eq tail d))
    · rcases List.mem_append.mp hp with hp|hp
      · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
        cases c with
        | inl c=>
          rcases ihT a r hr c with h|⟨d,h⟩
          · exact Or.inl (congrArg Sum.inl h)
          · exact Or.inr ⟨Sum.inl d,congrArg Sum.inl h⟩
        | inr c=>exact Or.inr ⟨Sum.inr c,rfl⟩
      · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
        cases c with
        | inl c=>exact Or.inr ⟨Sum.inl c,rfl⟩
        | inr c=>
          rcases ihV a r hr c with h|⟨d,h⟩
          · exact Or.inl (congrArg Sum.inr h)
          · exact Or.inr ⟨Sum.inr d,congrArg Sum.inr h⟩

theorem splitIndex_low_eq_of_high (T : ClockTree S as) (e c d : T.Slot)
    {U : ℕ} (hhigh : U≤T.splitIndex e c) (hlow : T.splitIndex c d<U) :
    T.splitIndex e d=T.splitIndex c d := by
  have hle : T.splitIndex c d≤T.splitIndex e d :=
    T.splitIndex_cut_trans _ e c d (by omega) le_rfl
  have hge : T.splitIndex e d≤T.splitIndex c d := by
    by_contra H
    have hec : T.splitIndex c d+1≤T.splitIndex c e := by
      rw [T.splitIndex_symm c e]
      omega
    have H':=T.splitIndex_cut_trans (T.splitIndex c d+1) c e d hec (by omega)
    omega
  omega

theorem NativePersistentLowForks.observedHigh {T : ClockTree S as} {i star U : ℕ}
    (hT : NativePersistentLowForks i star U T) (hi : i ≤ star) (hs : star < U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c)) :
    NativePersistentLowForks i star U p.tree := by
  have hem:=(T.markedAttach_embed_preserves a p hp).2
  have hmark (d : T.Slot) :
      p.tree.splitIndex p.mark (p.embed d)=i ∨
      p.tree.splitIndex p.mark (p.embed d)=star ∨
      U≤p.tree.splitIndex p.mark (p.embed d) := by
    rcases hT c d with H|H|H
    · have HD : p.tree.splitIndex (p.embed c) (p.embed d)<U := by rw [hem,H];omega
      exact Or.inl ((p.tree.splitIndex_low_eq_of_high p.mark (p.embed c) (p.embed d) hh HD).trans
        ((hem c d).trans H))
    · have HD : p.tree.splitIndex (p.embed c) (p.embed d)<U := by rw [hem,H];omega
      exact Or.inr (Or.inl ((p.tree.splitIndex_low_eq_of_high p.mark (p.embed c) (p.embed d) hh HD).trans
        ((hem c d).trans H)))
    · exact Or.inr (Or.inr (p.tree.splitIndex_cut_trans U p.mark (p.embed c) (p.embed d) hh
        (by rw [hem];exact H)))
  intro e d
  rcases markedAttach_slot_coverage T a p hp e with rfl|⟨e,rfl⟩
  · rcases markedAttach_slot_coverage T a p hp d with rfl|⟨d,rfl⟩
    · have H:=hT c c
      simpa only [splitIndex_self] using H
    · exact hmark d
  · rcases markedAttach_slot_coverage T a p hp d with rfl|⟨d,rfl⟩
    · rw [splitIndex_symm]
      exact hmark e
    · rw [hem]
      exact hT e d

theorem cavityLeft_splitIndex {B : Type} (T : ClockTree (S×B) as) (s t : T.Slot) :
    T.cavityLeft.splitIndex (T.cavityLeftSlot s) (T.cavityLeftSlot t)=T.splitIndex s t := by
  induction T with
  | leaf=>rfl
  | step b T ih=>exact congrArg (1+·) (ih s t)
  | fork T V ihT ihV=>cases s <;> cases t <;> first | rfl | exact ihT _ _ | exact ihV _ _

theorem NativePersistentLowForks.cavityLeft {B : Type} {T : ClockTree (S×B) as}
    {i star U : ℕ} (hT : NativePersistentLowForks i star U T) :
    NativePersistentLowForks i star U T.cavityLeft := by
  intro s t
  obtain ⟨s,rfl⟩:=(T.cavityLeftSlot).surjective s
  obtain ⟨t,rfl⟩:=(T.cavityLeftSlot).surjective t
  simpa only [cavityLeft_splitIndex] using hT s t

theorem NativePersistentLowForks.observedRestHigh {B : Type} {T : ClockTree (S×B) as}
    {i star U : ℕ} (hT : NativePersistentLowForks i star U T)
    (hi : i ≤ star) (hs : star < U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c)) :
    NativePersistentLowForks i star U p.tree.cavityLeft :=
  (hT.observedHigh hi hs a p hp c hh).cavityLeft

end OAI.SKFluctuations.Hierarchy.ClockTree
