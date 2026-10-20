module

public import ComparisonSignedCavityActualDummyScalarMarked
public import ComparisonSignedCavityHighFreshFullRowInterchange

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped NNReal
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
variable {S : Type}

theorem nativeFreshAtSlot_withDummy {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (s : T.Slot) (star : ℕ) :
    nativeFreshAtSlot T.withDummy a (T.withDummySlot s) star=
      (nativeFreshAtSlot T a s star).withDummy := by
  induction T generalizing a star with
  | leaf=>simpa only [withDummy,nativeFreshAtSlot] using
      (MarkedPlacement.withDummy_fresh (leaf (S:=S)) (a-1)).symm
  | step b T ih=>
    cases star with
    | zero=>simpa only [withDummy,nativeFreshAtSlot] using
        (MarkedPlacement.withDummy_fresh (T.step b) (a-b.val)).symm
    | succ star=>
      change (nativeFreshAtSlot T.withDummy b.val (T.withDummySlot s) star).step b=
        ((nativeFreshAtSlot T b.val s star).step b).withDummy
      rw [ih,MarkedPlacement.withDummy_step]
  | fork T R ihT ihR=>
    cases star with
    | zero=>simpa only [withDummy,nativeFreshAtSlot] using
        (MarkedPlacement.withDummy_fresh (T.fork R) (-a)).symm
    | succ star=>
      cases s with
      | inl s=>
        change (nativeFreshAtSlot T.withDummy a (T.withDummySlot s) (star+1)).left R.withDummy=
          ((nativeFreshAtSlot T a s (star+1)).left R).withDummy
        rw [ihT,MarkedPlacement.withDummy_left]
      | inr s=>
        change (nativeFreshAtSlot R.withDummy a (R.withDummySlot s) (star+1)).right T.withDummy=
          ((nativeFreshAtSlot R a s (star+1)).right T).withDummy
        rw [ihR,MarkedPlacement.withDummy_right]

theorem nativeHighMarkedRows_withDummy {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ) :
    nativeHighMarkedRows T.withDummy (T.withDummySlot s) star a=
      (nativeHighMarkedRows T s star a).map MarkedPlacement.withDummy := by
  induction T generalizing star a with
  | leaf=>rfl
  | step b T ih=>
    cases star with
    | zero=>
      simp only [withDummy,withDummySlot,nativeHighMarkedRows,markedAttach_withDummy,
        List.map_map,Function.comp_def,MarkedPlacement.withDummy_step]
    | succ star=>
      simp only [withDummy,withDummySlot,nativeHighMarkedRows,ih,List.map_map,
        Function.comp_def,MarkedPlacement.withDummy_step]
  | fork T R ihT ihR=>
    cases s with
    | inl s=>
      simp only [withDummy,withDummySlot,Equiv.sumCongr_apply,nativeHighMarkedRows,
        Sum.map_inl,ihT,List.map_map,Function.comp_def,MarkedPlacement.withDummy_left]
    | inr s=>
      simp only [withDummy,withDummySlot,Equiv.sumCongr_apply,nativeHighMarkedRows,
        Sum.map_inr,ihR,List.map_map,Function.comp_def,MarkedPlacement.withDummy_right]

theorem MarkedPlacement.withDummy_fresh_at_old {as : List PositiveMass}
    {T : ClockTree S as} (p : MarkedPlacement T) (a : ℝ) (s : T.Slot) (star : ℕ) :
    nativeFreshAtSlot p.withDummy.tree a (p.withDummy.embed (T.withDummySlot s)) star=
      (nativeFreshAtSlot p.tree a (p.embed s) star).withDummy := by
  change nativeFreshAtSlot p.tree.withDummy a (p.withDummy.embed (T.withDummySlot s)) star=_
  rw [p.withDummy_embed,nativeFreshAtSlot_withDummy]

theorem MarkedPlacement.withDummy_split_mark {as : List PositiveMass}
    {T : ClockTree S as} (p : MarkedPlacement T) (c : p.tree.Slot) :
    p.withDummy.tree.splitIndex (p.tree.withDummySlot c) p.withDummy.mark=p.tree.splitIndex c p.mark :=
  p.tree.splitIndex_withDummy c p.mark

theorem MarkedPlacement.withDummy_mark_eq {as : List PositiveMass}
    {T : ClockTree S as} (p : MarkedPlacement T) (c : p.tree.Slot) :
    p.withDummy.mark=p.tree.withDummySlot c ↔ p.mark=c :=
  p.tree.withDummySlot.injective.eq_iff

end OAI.SKFluctuations.Hierarchy.ClockTree
