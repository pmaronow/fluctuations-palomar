module

public import ComparisonSignedCavityObservedDiagramRestRead

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def NativeObservedDiagram.ValidRead (D : NativeObservedDiagram T) : Prop :=
  ∀σ c,T.atSlot (D.read σ) c=D.tree.atSlot σ (D.embed c)

theorem NativeObservedDiagram.validRead_identity (T : ClockTree S as) :
    (NativeObservedDiagram.identity T).ValidRead := fun _ _=>rfl

theorem NativeObservedDiagram.ValidRead.observe {D : NativeObservedDiagram T}
    (h : D.ValidRead) (p : MarkedPlacement D.tree) : (D.observe p).ValidRead := by
  intro σ c
  exact (h (p.restrict σ) c).trans (p.restrict_at σ (D.embed c))

theorem NativeObservedDiagram.ValidRead.fresh {D : NativeObservedDiagram T}
    (h : D.ValidRead) (s : T.Slot) (star : ℕ) (a : ℝ) : (D.fresh s star a).ValidRead := by
  intro σ c
  exact (h ((nativeFreshAtSlot D.tree a (D.embed s) star).restrict σ) c).trans
    ((nativeFreshAtSlot D.tree a (D.embed s) star).restrict_at σ (D.embed c))

theorem NativeProjectionSpine.validRead_graft {A V : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) {D : NativeObservedDiagram A} (hD : D.ValidRead) :
    (h.graftDiagram D).ValidRead := by
  induction h with
  | base=>exact hD
  | projection h a hl ih=>exact ih.fresh base.target star a

theorem native_observed_high_words_validRead (D : NativeObservedDiagram T)
    (hD : D.ValidRead) (s : T.Slot) (star k : ℕ)
    (z : ℝ×NativeObservedDiagram T) (hz : z∈nativeObservedHighWords D s star k) : z.2.ValidRead := by
  induction k generalizing D z with
  | zero=>
    simp only [nativeObservedHighWords,List.mem_singleton] at hz
    subst z
    exact hD
  | succ k ih=>
    simp only [nativeObservedHighWords,List.mem_flatMap,List.mem_map,nativeObservedHighRows] at hz
    obtain ⟨v,⟨p,hp,rfl⟩,u,hu,rfl⟩:=hz
    exact ih (D.observe p) (hD.observe p) u hu

variable {B : Type}

theorem NativeObservedDiagram.ValidRead.restRead_actual
    {A : ClockTree (S×B) as} {D : NativeObservedDiagram A} (hD : D.ValidRead)
    (σ : D.tree.Assignment) :
    D.restRead (D.tree.cavityAssignment σ).1=(A.cavityAssignment (D.read σ)).1 := by
  apply A.cavityLeft.assignment_ext
  intro c
  obtain ⟨d,rfl⟩:=A.cavityLeftSlot.surjective c
  rw [D.restRead_at,D.tree.atSlot_cavityLeft,A.atSlot_cavityLeft,hD σ d]

theorem NativeObservedDiagram.restMarks_actual {A : ClockTree (S×B) as}
    (D : NativeObservedDiagram A) (σ : D.tree.Assignment) :
    D.restMarks (D.tree.cavityAssignment σ).1=D.marks.map (fun c=>(D.tree.atSlot σ c).1) := by
  simp only [restMarks,D.tree.atSlot_cavityLeft]

end OAI.SKFluctuations.Hierarchy.ClockTree
