module

public import ComparisonSignedCavityActualDummyScalarTree

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped NNReal
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
variable {S : Type*}

theorem withDummy_single (as : List PositiveMass) :
    (single (S:=S) as).withDummy=single as := by
  induction as with
  | nil=>rfl
  | cons a as ih=>exact congrArg (ClockTree.step a) ih

theorem withDummy_singleSlot (as : List PositiveMass) :
    cast (congrArg ClockTree.Slot (withDummy_single (S:=S) as))
      ((single (S:=S) as).withDummySlot (singleSlot as))=singleSlot as := by
  induction as with
  | nil=>rfl
  | cons a as ih=>exact ih

namespace MarkedPlacement

theorem dummy_ext_topology {as : List PositiveMass} {T : ClockTree S as}
    (p r : MarkedPlacement T) (hT : p.tree=r.tree) (hc : p.coeff=r.coeff)
    (he : ∀s,cast (congrArg ClockTree.Slot hT) (p.embed s)=r.embed s)
    (hm : cast (congrArg ClockTree.Slot hT) p.mark=r.mark) : p=r := by
  cases p with
  | mk pt pc pr ps pe pm pR pS=>
    cases r with
    | mk rt rc rr rs re rm rR rS=>
      dsimp only at hT hc he hm
      cases hT
      cases hc
      simp only [cast_eq] at he hm
      have he' : pe=re:=funext he
      cases he'
      cases hm
      have hr : pr=rr := by
        funext σ
        exact T.assignment_ext (fun s=>(pR σ s).trans (rR σ s).symm)
      have hs : ps=rs :=funext fun σ=>(pS σ).trans (rS σ).symm
      cases hr
      cases hs
      rfl

def withDummy {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) : MarkedPlacement T.withDummy where
  tree:=p.tree.withDummy
  coeff:=p.coeff
  restrict:=fun σ=>T.withDummy.assignmentOfSlots (fun s=>p.tree.withDummy.atSlot σ
    (p.tree.withDummySlot (p.embed (T.withDummySlot.symm s))))
  spin:=fun σ=>p.tree.withDummy.atSlot σ (p.tree.withDummySlot p.mark)
  embed:=fun s=>p.tree.withDummySlot (p.embed (T.withDummySlot.symm s))
  mark:=p.tree.withDummySlot p.mark
  restrict_at:=fun _ _=>atSlot_assignmentOfSlots _ _ _
  spin_at:=fun _=>rfl

theorem withDummy_coeff {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) : p.withDummy.coeff=p.coeff := rfl

theorem withDummy_embed {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (s : T.Slot) :
    p.withDummy.embed (T.withDummySlot s)=p.tree.withDummySlot (p.embed s) := by
  simp only [withDummy,Equiv.symm_apply_apply]

theorem withDummy_physical_restrict {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (σ : p.tree.withDummy.Assignment) :
    T.withDummyPhysical (p.withDummy.restrict σ)=p.restrict (p.tree.withDummyPhysical σ) := by
  apply T.assignment_ext
  intro s
  rw [T.withDummyPhysical_atSlot,p.withDummy.restrict_at,p.withDummy_embed,p.restrict_at,
    p.tree.withDummyPhysical_atSlot]
  rfl

theorem withDummy_physical_spin {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (σ : p.tree.withDummy.Assignment) :
    (p.withDummy.spin σ).1=p.spin (p.tree.withDummyPhysical σ) := by
  rw [p.withDummy.spin_at,p.spin_at,p.tree.withDummyPhysical_atSlot]
  rfl

theorem withDummy_coincide : (coincide (S:=S)).withDummy=coincide := by
  apply dummy_ext_topology (coincide (S:=S)).withDummy coincide rfl rfl
  · intro s;rfl
  · rfl

theorem withDummy_step (a : PositiveMass) {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) : (p.step a).withDummy=p.withDummy.step a := by
  apply dummy_ext_topology (p.step a).withDummy (p.withDummy.step a) rfl rfl
  · intro s;rfl
  · rfl

theorem withDummy_left {as : List PositiveMass} {T : ClockTree S as}
    (R : ClockTree S as) (p : MarkedPlacement T) :
    (p.left R).withDummy=p.withDummy.left R.withDummy := by
  apply dummy_ext_topology (p.left R).withDummy (p.withDummy.left R.withDummy) rfl rfl
  · intro s
    cases s with
    | inl s=>rfl
    | inr s=>
      change Sum.inr (R.withDummySlot (R.withDummySlot.symm s))=Sum.inr s
      rw [Equiv.apply_symm_apply]
  · rfl

theorem withDummy_right {as : List PositiveMass} (T : ClockTree S as)
    {R : ClockTree S as} (p : MarkedPlacement R) :
    (p.right T).withDummy=p.withDummy.right T.withDummy := by
  apply dummy_ext_topology (p.right T).withDummy (p.withDummy.right T.withDummy) rfl rfl
  · intro s
    cases s with
    | inl s=>
      change Sum.inl (T.withDummySlot (T.withDummySlot.symm s))=Sum.inl s
      rw [Equiv.apply_symm_apply]
    | inr s=>rfl
  · rfl

theorem withDummy_fresh {as : List PositiveMass} (T : ClockTree S as) (c : ℝ) :
    (fresh T c).withDummy=fresh T.withDummy c := by
  have hT : (fresh T c).withDummy.tree=(fresh T.withDummy c).tree :=
    congrArg (ClockTree.fork T.withDummy) (withDummy_single as)
  apply dummy_ext_topology _ _ hT rfl
  · intro s
    change cast _ (Sum.inl (T.withDummySlot (T.withDummySlot.symm s)))=Sum.inl s
    rw [Equiv.apply_symm_apply]
    exact dummy_cast_sum_inl rfl (congrArg ClockTree.Slot (withDummy_single (S:=S) as)) _ _
  · change cast _ (Sum.inr ((single (S:=S) as).withDummySlot (singleSlot as)))=Sum.inr (singleSlot as)
    exact (dummy_cast_sum_inr rfl (congrArg ClockTree.Slot (withDummy_single (S:=S) as)) _ _).trans
      (congrArg Sum.inr (withDummy_singleSlot (S:=S) as))

end MarkedPlacement

theorem markedAttach_withDummy {as : List PositiveMass} (T : ClockTree S as) (a : ℝ) :
    T.withDummy.markedAttach a=(T.markedAttach a).map MarkedPlacement.withDummy := by
  induction T generalizing a with
  | leaf=>simp only [withDummy,markedAttach,List.map_cons,List.map_nil,
      MarkedPlacement.withDummy_coincide,MarkedPlacement.withDummy_fresh]
  | step b T ih=>
    simp only [withDummy,markedAttach,ih,List.map_cons,List.map_map,
      Function.comp_def,MarkedPlacement.withDummy_fresh,MarkedPlacement.withDummy_step]
  | fork T R ihT ihR=>
    simp only [withDummy,markedAttach,ihT,ihR,List.map_cons,List.map_append,List.map_map,
      Function.comp_def,MarkedPlacement.withDummy_fresh,MarkedPlacement.withDummy_left,
      MarkedPlacement.withDummy_right]

end OAI.SKFluctuations.Hierarchy.ClockTree
