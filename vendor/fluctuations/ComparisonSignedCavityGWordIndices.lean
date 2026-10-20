module

public import ComparisonSignedCavityObservedWordGeometry
public import ComparisonSignedCavityActualAuxiliaryGammaTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def nativeObservedErrorIndex (D : NativeObservedDiagram T) : ℕ :=
  match D.marks with
  | f::e::_=>D.tree.splitIndex e f
  | _=>0

theorem native_observed_error_index_fresh (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (a : ℝ) (hk : 2 ≤ D.marks.length) :
    nativeObservedErrorIndex (D.fresh s star a)=nativeObservedErrorIndex D := by
  cases hm : D.marks with
  | nil=>simp only [hm,List.length_nil] at hk;omega
  | cons f tail=>
    cases tail with
    | nil=>simp only [hm,List.length_cons,List.length_nil] at hk;omega
    | cons e tail=>
      simp only [nativeObservedErrorIndex,NativeObservedDiagram.fresh,hm,List.map_cons,
        List.cons_append,(nativeFreshAtSlot_old_splits D.tree a (D.embed s) star).2]

theorem NativeProjectionSpine.graft_error_index {A V : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A) (hk : 2 ≤ D.marks.length) :
    nativeObservedErrorIndex (h.graftDiagram D)=nativeObservedErrorIndex D := by
  induction h with
  | base=>rfl
  | projection h a hl ih=>
    change nativeObservedErrorIndex ((h.graftDiagram D).fresh base.target star a)=_
    rw [native_observed_error_index_fresh]
    · exact ih
    · rw [h.graft_marks_length_all]
      omega

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeObservedGScalar {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (D : NativeObservedDiagram T) (s : T.Slot) (U : ℕ) (K : ℕ→ℝ) : ℝ :=
  match D.marks with
  | f::e::c::_=>(1/2:ℝ)*fullScalarCutConnected4 D.tree U K (D.embed s) c e f
  | _=>0

theorem native_observed_G_scalar_fresh {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (D : NativeObservedDiagram T)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ) (K : ℕ→ℝ) (hk : 3 ≤ D.marks.length) :
    nativeObservedGScalar (D.fresh s star 0) s U K=nativeObservedGScalar D s U K := by
  cases hm : D.marks with
  | nil=>simp only [hm,List.length_nil] at hk;omega
  | cons f tail=>
    cases tail with
    | nil=>simp only [hm,List.length_cons,List.length_nil] at hk;omega
    | cons e tail=>
      cases tail with
      | nil=>simp only [hm,List.length_cons,List.length_nil] at hk;omega
      | cons c tail=>
        simp only [nativeObservedGScalar,NativeObservedDiagram.fresh,hm,List.map_cons,List.cons_append]
        rw [native_full_connected_four_marked_preserves D.tree ho U K (D.embed s) c e f
          (nativeFreshAtSlot D.tree 0 (D.embed s) star) (nativeFreshAtSlot_mem D.tree 0 (D.embed s) star)]

end OAI.SKFluctuations.Cavity
