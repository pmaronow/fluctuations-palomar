module

public import ComparisonSignedCavityGWordIndices

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def nativeObservedTargetMetadata (D : NativeObservedDiagram T) (s : T.Slot) : ℕ×Bool :=
  match D.marks with
  | _::_::c::_=>(D.tree.splitIndex (D.embed s) c,decide (D.embed s=c))
  | _=>(0,true)

theorem native_observed_target_metadata_fresh (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (a : ℝ) (hk : 3 ≤ D.marks.length) :
    nativeObservedTargetMetadata (D.fresh s star a) s=nativeObservedTargetMetadata D s := by
  cases hm : D.marks with
  | nil=>simp only [hm,List.length_nil] at hk;omega
  | cons f tail=>
    cases tail with
    | nil=>simp only [hm,List.length_cons,List.length_nil] at hk;omega
    | cons e tail=>
      cases tail with
      | nil=>simp only [hm,List.length_cons,List.length_nil] at hk;omega
      | cons c tail=>
        simp only [nativeObservedTargetMetadata,NativeObservedDiagram.fresh,hm,List.map_cons,
          List.cons_append,(nativeFreshAtSlot_old_splits D.tree a (D.embed s) star).2,
          (nativeFreshAtSlot_old_splits D.tree a (D.embed s) star).1.eq_iff]

theorem NativeProjectionSpine.graft_target_metadata {A V : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A) (hk : 3 ≤ D.marks.length) :
    nativeObservedTargetMetadata (h.graftDiagram D) base.target=nativeObservedTargetMetadata D base.target := by
  induction h with
  | base=>rfl
  | projection h a hl ih=>
    change nativeObservedTargetMetadata ((h.graftDiagram D).fresh base.target star a) base.target=_
    rw [native_observed_target_metadata_fresh]
    · exact ih
    · rw [h.graft_marks_length_all]
      omega

end OAI.SKFluctuations.Hierarchy.ClockTree
