module

public import ComparisonSignedCavityObservedDiagramRestRead

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def nativeObservedMarkedGeometry (D : NativeObservedDiagram T) (s : T.Slot) (k : ℕ) :=
  ((D.marks.take k).map (fun c=>(D.tree.splitIndex (D.embed s) c,decide (D.embed s=c))),
    (D.marks.take k).map (fun c=>(D.marks.take k).map
      (fun e=>(D.tree.splitIndex c e,decide (c=e)))))

theorem native_observed_marked_geometry_fresh (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (a : ℝ) (k : ℕ) (hk : k ≤ D.marks.length) :
    nativeObservedMarkedGeometry (D.fresh s star a) s k=nativeObservedMarkedGeometry D s k := by
  have hl : k ≤ (D.marks.map (nativeFreshAtSlot D.tree a (D.embed s) star).embed).length := by
    simpa only [List.length_map] using hk
  simp only [nativeObservedMarkedGeometry,NativeObservedDiagram.fresh,
    List.take_append_of_le_length hl,List.map_take,List.map_map,Function.comp_def,
    (nativeFreshAtSlot_old_splits D.tree a (D.embed s) star).2,
    (nativeFreshAtSlot_old_splits D.tree a (D.embed s) star).1.eq_iff]

theorem NativeProjectionSpine.graft_marks_length_all {A V : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A) :
    (h.graftDiagram D).marks.length=D.marks.length+h.toothCount := by
  induction h with
  | base=>simp only [graftDiagram,id_eq,toothCount,Nat.add_zero]
  | projection h a hl ih=>
    simp only [graftDiagram,NativeObservedDiagram.fresh,List.length_append,List.length_map,
      List.length_singleton,toothCount,ih,Nat.add_assoc]

theorem NativeProjectionSpine.graft_marked_geometry {A V : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A) :
    nativeObservedMarkedGeometry (h.graftDiagram D) base.target D.marks.length=
      nativeObservedMarkedGeometry D base.target D.marks.length := by
  induction h with
  | base=>rfl
  | projection h a hl ih=>
    change nativeObservedMarkedGeometry ((h.graftDiagram D).fresh base.target star a)
      base.target D.marks.length=_
    rw [native_observed_marked_geometry_fresh]
    · exact ih
    · rw [h.graft_marks_length_all]
      omega

end OAI.SKFluctuations.Hierarchy.ClockTree
