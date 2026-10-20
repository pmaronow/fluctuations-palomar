module

public import ComparisonSignedCavityActualGWordScalarRate
public import ComparisonSignedCavityActualOriginalGPairingTransport
public import ComparisonSignedCavityActualTripleGValue

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def nativeObservedGSupport (D : NativeObservedDiagram T) (s : T.Slot) (U : ℕ) : Prop :=
  match D.marks with
  | f::e::c::_=>U≤D.tree.splitIndex (D.embed s) c ∧
      U≤D.tree.splitIndex (D.embed s) e ∧ U≤D.tree.splitIndex (D.embed s) f ∧
      e≠f ∧ D.embed s≠c
  | _=>False

theorem native_observed_G_support_fresh (D : NativeObservedDiagram T)
    (s : T.Slot) (star U : ℕ) (a : ℝ) (hk : 3 ≤ D.marks.length) :
    nativeObservedGSupport (D.fresh s star a) s U ↔ nativeObservedGSupport D s U := by
  obtain ⟨f,e,c,tail,he⟩:=native_observed_three_marks D hk
  simp only [nativeObservedGSupport,NativeObservedDiagram.fresh,he,List.map_cons,
    List.cons_append,ne_eq,(nativeFreshAtSlot_old_splits D.tree a (D.embed s) star).2,
    (nativeFreshAtSlot_old_splits D.tree a (D.embed s) star).1.eq_iff]

theorem NativeProjectionSpine.graft_G_support {A V : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A)
    (hk : 3 ≤ D.marks.length) (U : ℕ) :
    nativeObservedGSupport (h.graftDiagram D) base.target U ↔
      nativeObservedGSupport D base.target U := by
  induction h with
  | base=>rfl
  | projection h a hl ih=>
    change nativeObservedGSupport ((h.graftDiagram D).fresh base.target star a) base.target U ↔ _
    rw [native_observed_G_support_fresh]
    · exact ih
    · rw [h.graft_marks_length_all];omega

theorem NativeProjectionSpine.graft_leaves_le {A V : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest V} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A) :
    (h.graftDiagram D).tree.leaves ≤ D.tree.leaves+h.toothCount := by
  induction h with
  | base=>simp only [graftDiagram,id_eq,toothCount,Nat.add_zero,le_refl]
  | projection h a hl ih=>
    have H:=(h.graftDiagram D).tree.markedAttach_leaves a
      (nativeFreshAtSlot (h.graftDiagram D).tree a ((h.graftDiagram D).embed base.target) star)
      (nativeFreshAtSlot_mem (h.graftDiagram D).tree a ((h.graftDiagram D).embed base.target) star)
    change (nativeFreshAtSlot (h.graftDiagram D).tree a ((h.graftDiagram D).embed base.target) star).tree.leaves≤_
    simp only [toothCount]
    omega

theorem native_three_mark_leaves_le (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0) :
    z.tree.leaves ≤ T.leaves+3 := by
  have H1:=T.markedAttach_leaves 0 p hp
  have H2:=p.tree.markedAttach_leaves 0 r hr
  have H3:=r.tree.markedAttach_leaves 0 z hz
  omega

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_observed_G_scalar_zero_of_not_support
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (D : NativeObservedDiagram T) (ho : MassOrdered 0 as) (s : T.Slot)
    (U : ℕ) (K : ℕ→ℝ) (hU : U≤as.length) (hk : 3≤D.marks.length)
    (hef : U≤nativeObservedErrorIndex D) (hs : ¬nativeObservedGSupport D s U) :
    nativeObservedGScalar D s U K=0 := by
  obtain ⟨f,e,c,tail,he⟩:=native_observed_three_marks D hk
  simp only [nativeObservedGScalar,he]
  by_cases hac : D.embed s=c
  · rw [←hac,fullScalarCutConnected4_target_self_zero D.tree ho U K,mul_zero]
  · have H:=fullScalarCutConnected4_actual_block_support D.tree ho U K (D.embed s) c e f hU
      (by simpa only [nativeObservedErrorIndex,he] using hef)
    have Hnot : ¬(U≤D.tree.splitIndex (D.embed s) c ∧ U≤D.tree.splitIndex (D.embed s) e ∧
        U≤D.tree.splitIndex (D.embed s) f ∧ e≠f) := by
      intro HH
      apply hs
      simp only [nativeObservedGSupport,he]
      exact ⟨HH.1,HH.2.1,HH.2.2.1,HH.2.2.2,hac⟩
    rw [ite_eq_right Hnot] at H
    rw [H,mul_zero]

end OAI.SKFluctuations.Cavity
