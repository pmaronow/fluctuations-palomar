module

public import ComparisonSignedCavityHighFreshFullRowInterchange

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

structure NativeObservedDiagram (T : ClockTree S as) where
  tree : ClockTree S as
  embed : T.Slot→tree.Slot
  marks : List tree.Slot
  read : tree.Assignment→T.Assignment

def NativeObservedDiagram.step {T : ClockTree S as}
    (D : NativeObservedDiagram T) (b : PositiveMass) : NativeObservedDiagram (T.step b) where
  tree:=D.tree.step b
  embed:=D.embed
  marks:=D.marks
  read:=D.read

def NativeObservedDiagram.left {T : ClockTree S as}
    (D : NativeObservedDiagram T) (V : ClockTree S as) : NativeObservedDiagram (T.fork V) where
  tree:=D.tree.fork V
  embed:=Sum.map D.embed id
  marks:=D.marks.map Sum.inl
  read:=fun σ=>(D.read σ.1,σ.2)

def NativeObservedDiagram.right {V : ClockTree S as}
    (D : NativeObservedDiagram V) (T : ClockTree S as) : NativeObservedDiagram (T.fork V) where
  tree:=T.fork D.tree
  embed:=Sum.map id D.embed
  marks:=D.marks.map Sum.inr
  read:=fun σ=>(σ.1,D.read σ.2)

def nativeFreshHighDiagram (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T a s star).tree) : NativeObservedDiagram T where
  tree:=p.tree
  embed:=fun c=>p.embed ((nativeFreshAtSlot T a s star).embed c)
  marks:=[p.mark,p.embed (nativeFreshAtSlot T a s star).mark]
  read:=fun σ=>(nativeFreshAtSlot T a s star).restrict (p.restrict σ)

def nativeHighFreshDiagram (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (r : MarkedPlacement T) : NativeObservedDiagram T where
  tree:=(nativeFreshAtSlot r.tree a (r.embed s) star).tree
  embed:=fun c=>(nativeFreshAtSlot r.tree a (r.embed s) star).embed (r.embed c)
  marks:=[(nativeFreshAtSlot r.tree a (r.embed s) star).embed r.mark,
    (nativeFreshAtSlot r.tree a (r.embed s) star).mark]
  read:=fun σ=>r.restrict ((nativeFreshAtSlot r.tree a (r.embed s) star).restrict σ)

def NativeHighFreshDiagramRelation (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (p : MarkedPlacement (nativeFreshAtSlot T a s star).tree) (r : MarkedPlacement T) : Prop :=
  p.coeff=r.coeff ∧ nativeFreshHighDiagram T s star a p=nativeHighFreshDiagram T s star a r

theorem native_high_fresh_diagram_rows
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (aFresh aRow : ℝ) :
    List.Forall₂ (NativeHighFreshDiagramRelation T s star aFresh)
      (nativeHighMarkedRows (nativeFreshAtSlot T aFresh s star).tree
        ((nativeFreshAtSlot T aFresh s star).embed s) star aRow)
      (nativeHighMarkedRows T s star aRow) := by
  induction T generalizing star aFresh aRow with
  | leaf =>
    have hz:star=0:=by simpa using hstar
    subst star
    exact List.Forall₂.nil
  | @step b as T ih =>
    cases star with
    | zero =>
      simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.fresh,MarkedPlacement.left]
      rw [List.forall₂_map_left_iff]
      apply List.forall₂_same.mpr
      intro r hr
      refine ⟨rfl,?_⟩
      obtain ⟨d,hd⟩:=nativeFreshAtSlot_zero_eq_fresh_full r.tree aFresh (r.embed s)
      unfold nativeFreshHighDiagram nativeHighFreshDiagram
      rw [hd]
      rfl
    | succ star =>
      simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.step]
      apply List.rel_map (fun p r H=>?_) (ih s star (by simpa using hstar) b.val b.val)
      rcases H with ⟨hc,hd⟩
      refine ⟨hc,?_⟩
      exact congrArg (fun D=>D.step b) hd
  | @fork as T V ihT ihV =>
    cases star with
    | zero =>
      simp only [nativeFreshAtSlot,nativeHighMarkedRows,MarkedPlacement.fresh,MarkedPlacement.left]
      rw [List.forall₂_map_left_iff]
      apply List.forall₂_same.mpr
      intro r hr
      refine ⟨rfl,?_⟩
      obtain ⟨d,hd⟩:=nativeFreshAtSlot_zero_eq_fresh_full r.tree aFresh (r.embed s)
      unfold nativeFreshHighDiagram nativeHighFreshDiagram
      rw [hd]
      rfl
    | succ star =>
      cases s with
      | inl s =>
        simp only [nativeFreshAtSlot,nativeHighMarkedRows]
        apply List.rel_map (fun p r H=>?_) (ihT s (star+1) hstar aFresh aRow)
        rcases H with ⟨hc,hd⟩
        refine ⟨hc,?_⟩
        convert congrArg (fun D=>D.left V) hd using 1 <;>
          simp only [nativeFreshHighDiagram,nativeHighFreshDiagram,NativeObservedDiagram.left,
            nativeFreshAtSlot,MarkedPlacement.left,List.map_cons,List.map_nil] <;>
          congr 1 <;> funext c <;> cases c <;> rfl
      | inr s =>
        simp only [nativeFreshAtSlot,nativeHighMarkedRows]
        apply List.rel_map (fun p r H=>?_) (ihV s (star+1) hstar aFresh aRow)
        rcases H with ⟨hc,hd⟩
        refine ⟨hc,?_⟩
        convert congrArg (fun D=>D.right T) hd using 1 <;>
          simp only [nativeFreshHighDiagram,nativeHighFreshDiagram,NativeObservedDiagram.right,
            nativeFreshAtSlot,MarkedPlacement.right,List.map_cons,List.map_nil] <;>
          congr 1 <;> funext c <;> cases c <;> rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
