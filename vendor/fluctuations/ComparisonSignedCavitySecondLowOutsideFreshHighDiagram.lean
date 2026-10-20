module

public import ComparisonSignedCavityHighFreshDiagram
public import ComparisonSignedCavityHighOutsideCommutation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem native_second_low_outside_fresh_high_diagram_zero
    (T : ClockTree S as) (b c : T.Slot) (high : ℕ) (aFresh aRow : ℝ) :
    List.Forall₂ (NativeHighFreshDiagramRelation T b 0 aFresh)
      (nativeHighMarkedRows (nativeFreshAtSlot T aFresh b 0).tree
        ((nativeFreshAtSlot T aFresh b 0).embed c) high aRow)
      (nativeHighMarkedRows T c high aRow) := by
  cases T
  all_goals simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.fresh,MarkedPlacement.left]
  all_goals first | exact List.Forall₂.nil | skip
  all_goals rw [List.forall₂_map_left_iff]
  all_goals apply List.forall₂_same.mpr
  all_goals intro r _hr
  all_goals refine ⟨rfl,?_⟩
  all_goals obtain ⟨e,he⟩:=nativeFreshAtSlot_zero_eq_fresh_full r.tree aFresh (r.embed b)
  all_goals unfold nativeFreshHighDiagram nativeHighFreshDiagram
  all_goals rw [he]
  all_goals rfl

theorem native_second_low_outside_fresh_high_diagram_rows
    (T : ClockTree S as) (b c : T.Slot) (star high : ℕ)
    (hstar : star≤as.length) (hhigh : star≤high) (aFresh aRow : ℝ) :
    List.Forall₂ (NativeHighFreshDiagramRelation T b star aFresh)
      (nativeHighMarkedRows (nativeFreshAtSlot T aFresh b star).tree
        ((nativeFreshAtSlot T aFresh b star).embed c) high aRow)
      (nativeHighMarkedRows T c high aRow) := by
  induction T generalizing star high aFresh aRow with
  | leaf=>
    have HS : star=0:=by simpa using hstar
    subst star
    exact native_second_low_outside_fresh_high_diagram_zero .leaf b c high aFresh aRow
  | @step m as T ih=>
    cases star with
    | zero=>exact native_second_low_outside_fresh_high_diagram_zero (T.step m) b c high aFresh aRow
    | succ star=>
      cases high with
      | zero=>omega
      | succ high=>
        simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.step]
        apply List.rel_map (fun p r H=>?_) (ih b c star high (by simpa using hstar) (by omega) m.val m.val)
        rcases H with ⟨hc,hd⟩
        refine ⟨hc,?_⟩
        exact congrArg (fun D=>D.step m) hd
  | @fork as T V ihT ihV=>
    cases star with
    | zero=>exact native_second_low_outside_fresh_high_diagram_zero (T.fork V) b c high aFresh aRow
    | succ star=>
      cases b with
      | inl b=>
        cases c with
        | inl c=>
          simp only [nativeFreshAtSlot,nativeHighMarkedRows]
          apply List.rel_map (fun p r H=>?_) (ihT b c (star+1) high hstar hhigh aFresh aRow)
          rcases H with ⟨hc,hd⟩
          refine ⟨hc,?_⟩
          convert congrArg (fun D=>D.left V) hd using 1 <;>
            simp only [nativeFreshHighDiagram,nativeHighFreshDiagram,NativeObservedDiagram.left,
              nativeFreshAtSlot,MarkedPlacement.left,List.map_cons,List.map_nil] <;>
            congr 1 <;> funext s <;> cases s <;> rfl
        | inr c=>
          simp only [nativeFreshAtSlot,nativeHighMarkedRows]
          simp_rw [nativeHighRows_marked_left_cross]
          rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
          apply List.forall₂_same.mpr
          intro r _hr
          refine ⟨rfl,?_⟩
          simp only [nativeFreshHighDiagram,nativeHighFreshDiagram,nativeFreshAtSlot,
            MarkedPlacement.left,MarkedPlacement.right]
          congr 1
          funext s
          cases s <;> rfl
      | inr b=>
        cases c with
        | inl c=>
          simp only [nativeFreshAtSlot,nativeHighMarkedRows]
          simp_rw [nativeHighRows_marked_right_cross]
          rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff]
          apply List.forall₂_same.mpr
          intro r _hr
          refine ⟨rfl,?_⟩
          simp only [nativeFreshHighDiagram,nativeHighFreshDiagram,nativeFreshAtSlot,
            MarkedPlacement.left,MarkedPlacement.right]
          congr 1
          funext s
          cases s <;> rfl
        | inr c=>
          simp only [nativeFreshAtSlot,nativeHighMarkedRows]
          apply List.rel_map (fun p r H=>?_) (ihV b c (star+1) high hstar hhigh aFresh aRow)
          rcases H with ⟨hc,hd⟩
          refine ⟨hc,?_⟩
          convert congrArg (fun D=>D.right T) hd using 1 <;>
            simp only [nativeFreshHighDiagram,nativeHighFreshDiagram,NativeObservedDiagram.right,
              nativeFreshAtSlot,MarkedPlacement.right,List.map_cons,List.map_nil] <;>
            congr 1 <;> funext s <;> cases s <;> rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
