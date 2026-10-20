module

public import ComparisonSignedCavityProjectionSpineWordDiagram
public import ComparisonSignedCavityStarFieldFreshTestFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass} {T : ClockTree (S×B) as}

def NativeObservedDiagram.restRead (D : NativeObservedDiagram T)
    (σ : D.tree.cavityLeft.Assignment) : T.cavityLeft.Assignment :=
  assignmentOfSlots T.cavityLeft (fun c=>D.tree.cavityLeft.atSlot σ
    (D.tree.cavityLeftSlot (D.embed (T.cavityLeftSlot.symm c))))

theorem NativeObservedDiagram.restRead_at (D : NativeObservedDiagram T)
    (σ : D.tree.cavityLeft.Assignment) (c : T.Slot) :
    T.cavityLeft.atSlot (D.restRead σ) (T.cavityLeftSlot c)=
      D.tree.cavityLeft.atSlot σ (D.tree.cavityLeftSlot (D.embed c)) := by
  simp only [restRead,atSlot_assignmentOfSlots,Equiv.symm_apply_apply]

def NativeObservedDiagram.restMarks (D : NativeObservedDiagram T)
    (σ : D.tree.cavityLeft.Assignment) : List S :=
  D.marks.map (fun c=>D.tree.cavityLeft.atSlot σ (D.tree.cavityLeftSlot c))

theorem NativeObservedDiagram.restRead_fresh (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (a : ℝ)
    (σ : (D.fresh s star a).tree.cavityLeft.Assignment) :
    (D.fresh s star a).restRead σ=
      D.restRead ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict σ) := by
  apply T.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=T.cavityLeftSlot.surjective c
  rw [restRead_at,restRead_at]
  exact ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict_at σ (D.embed d)).symm

theorem NativeObservedDiagram.restMarks_fresh (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (a : ℝ)
    (σ : (D.fresh s star a).tree.cavityLeft.Assignment) :
    (D.fresh s star a).restMarks σ=
      D.restMarks ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict σ)++
        [(nativeFreshAtSlot D.tree a (D.embed s) star).restSpin σ] := by
  simp only [restMarks,fresh,List.map_append,List.map_map,List.map_singleton,Function.comp_def,
    MarkedPlacement.restSpin]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact ((nativeFreshAtSlot D.tree a (D.embed s) star).restRestrict_at σ c).symm

theorem NativeObservedDiagram.restMarks_length (D : NativeObservedDiagram T)
    (σ : D.tree.cavityLeft.Assignment) : (D.restMarks σ).length=D.marks.length := by
  simp only [restMarks,List.length_map]

theorem NativeProjectionSpine.graft_marks_length {A V : ClockTree (S×B) as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A) :
    (h.graftDiagram D).marks.length=D.marks.length+h.toothCount := by
  induction h with
  | base=>simp only [graftDiagram,id_eq,toothCount,Nat.add_zero]
  | projection h a hl ih=>
    simp only [graftDiagram,NativeObservedDiagram.fresh,List.length_append,List.length_map,
      List.length_singleton,toothCount,ih,Nat.add_assoc]

end OAI.SKFluctuations.Hierarchy.ClockTree
