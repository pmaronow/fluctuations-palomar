module

public import ComparisonSignedCavityOutsideMarkedRows
public import ComparisonSignedCavityHighRowsCommutationReadout

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

namespace NativeTwoHighPlacement

theorem ofTwo_fresh_commute {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (c : ℝ) :
    ofTwo p (MarkedPlacement.fresh p.tree c)=
      (ofTwo (MarkedPlacement.fresh T c) (p.left (ClockTree.single as))).swap := by
  unfold ofTwo swap MarkedPlacement.fresh MarkedPlacement.left
  congr 1
  ring

end NativeTwoHighPlacement

def nativeHighOutsidePlacements {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) (star : ℕ) (a : ℝ) : List (NativeTwoHighPlacement T) :=
  (nativeHighMarkedRows T s star a).flatMap fun p=>
    (nativeOutsideMarkedRows p.tree (p.embed s) star a).map (NativeTwoHighPlacement.ofTwo p)

def nativeOutsideHighPlacements {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) (star : ℕ) (a : ℝ) : List (NativeTwoHighPlacement T) :=
  (nativeOutsideMarkedRows T s star a).flatMap fun p=>
    (nativeHighMarkedRows p.tree (p.embed s) star a).map (fun r=>(NativeTwoHighPlacement.ofTwo p r).swap)

theorem nativeHighRows_after_fresh {as : List PositiveMass} (T : ClockTree S as)
    (c : ℝ) (s : T.Slot) (star : ℕ) (a : ℝ) :
    nativeHighMarkedRows (MarkedPlacement.fresh T c).tree
      ((MarkedPlacement.fresh T c).embed s) star a=
      (nativeHighMarkedRows T s star a).map (fun p=>p.left (ClockTree.single as)) := rfl

theorem nativeOutsideRows_after_step {as : List PositiveMass} {T : ClockTree S as}
    (b : PositiveMass) (p : MarkedPlacement T) (s : T.Slot) (star : ℕ) (a : ℝ) :
    nativeOutsideMarkedRows (p.step b).tree ((p.step b).embed s) (star+1) a=
      MarkedPlacement.fresh ((p.step b).tree) (a-b.val)::
        (nativeOutsideMarkedRows p.tree (p.embed s) star b.val).map (fun r=>r.step b) := rfl

theorem nativeOutsideRows_after_step_zero {as : List PositiveMass} {T : ClockTree S as}
    (b : PositiveMass) (p : MarkedPlacement T) (s : T.Slot) (a : ℝ) :
    nativeOutsideMarkedRows (p.step b).tree ((p.step b).embed s) 0 a=
      [MarkedPlacement.fresh ((p.step b).tree) (a-b.val)] := rfl

theorem nativeOutsideRows_marked_left {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : MarkedPlacement T) (s : T.Slot) (star : ℕ) (a : ℝ) :
    nativeOutsideMarkedRows (p.left V).tree ((p.left V).embed (Sum.inl s)) star a=
      MarkedPlacement.fresh ((p.left V).tree) (-a)::
        ((nativeOutsideMarkedRows p.tree (p.embed s) star a).map (fun r=>r.left V)++
         (V.markedAttach a).map (fun r=>r.right p.tree)) := rfl

theorem nativeOutsideRows_marked_right {as : List PositiveMass} (T : ClockTree S as)
    {V : ClockTree S as} (p : MarkedPlacement V) (s : V.Slot) (star : ℕ) (a : ℝ) :
    nativeOutsideMarkedRows (p.right T).tree ((p.right T).embed (Sum.inr s)) star a=
      MarkedPlacement.fresh ((p.right T).tree) (-a)::
        ((T.markedAttach a).map (fun r=>r.left p.tree)++
         (nativeOutsideMarkedRows p.tree (p.embed s) star a).map (fun r=>r.right T)) := rfl

theorem native_flatMap_singleton_map {α β : Type} (xs : List α) (f : α→β) :
    (xs.flatMap (fun x=>[f x]))=xs.map f := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simpa only [List.flatMap_cons,List.map_cons,List.singleton_append] using congrArg (List.cons (f x)) ih

theorem native_flatMap_cons_perm {α β : Type} (xs : List α) (f : α→β) (g : α→List β) :
    (xs.flatMap (fun x=>f x::g x)).Perm (xs.map f++xs.flatMap g) :=
  (List.map_append_flatMap_perm xs f g).symm

theorem native_high_outside_placements_commute {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ) :
    (nativeHighOutsidePlacements T s star a).Perm
      (nativeOutsideHighPlacements T s star a) := by
  induction T generalizing star a with
  | leaf=>
    simp [nativeHighOutsidePlacements,nativeOutsideHighPlacements,nativeHighMarkedRows,
      nativeOutsideMarkedRows,markedAttach,MarkedPlacement.coincide,MarkedPlacement.fresh]
  | @step b as T ih=>
    cases star with
    | zero=>
      simp only [nativeHighOutsidePlacements,nativeOutsideHighPlacements,nativeHighMarkedRows,
        nativeOutsideMarkedRows,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,
        List.append_nil]
      simp_rw [nativeOutsideRows_after_step_zero,List.map_cons,List.map_nil,native_flatMap_singleton_map]
      simp_rw [nativeHighRows_after_fresh,List.map_map,Function.comp_def,
        NativeTwoHighPlacement.ofTwo_fresh_commute]
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def]
      exact List.Perm.refl _
    | succ star=>
      have H:=ih s star b.val
      unfold nativeHighOutsidePlacements nativeOutsideHighPlacements at H ⊢
      simp only [nativeHighMarkedRows,nativeOutsideMarkedRows,List.flatMap_map,
        List.flatMap_cons]
      simp_rw [nativeOutsideRows_after_step,List.map_cons,List.map_map,Function.comp_def,
        NativeTwoHighPlacement.ofTwo_step,nativeHighRows_after_fresh,List.map_map,Function.comp_def,
        NativeTwoHighPlacement.ofTwo_fresh_commute,nativeHighRows_marked_step,
        List.map_map,Function.comp_def,NativeTwoHighPlacement.ofTwo_step,
        NativeTwoHighPlacement.swap_step]
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def]
      have HS:=H.map (NativeTwoHighPlacement.step b)
      simp only [List.map_flatMap,List.map_map,Function.comp_def] at HS
      exact (native_flatMap_cons_perm _ _ _).trans ((List.Perm.refl _).append HS)
  | @fork as T V ihT ihV=>
    cases s with
    | inl s=>
      have H:=ihT s star a
      unfold nativeHighOutsidePlacements nativeOutsideHighPlacements at H ⊢
      simp only [nativeHighMarkedRows,nativeOutsideMarkedRows,List.flatMap_map,
        List.flatMap_cons,List.flatMap_append]
      simp_rw [nativeOutsideRows_marked_left]
      simp_rw [List.map_cons,List.map_append,List.map_map,Function.comp_def,
        nativeHighRows_after_fresh,NativeTwoHighPlacement.ofTwo_fresh_commute,
        nativeHighRows_marked_left,nativeHighRows_marked_right_cross,
        List.map_map,Function.comp_def,NativeTwoHighPlacement.ofTwo_left,
        NativeTwoHighPlacement.swap_left,NativeTwoHighPlacement.ofTwo_across,
        NativeTwoHighPlacement.ofTwo_across_swapped]
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def]
      have HL:=H.map (NativeTwoHighPlacement.left V)
      simp only [List.map_flatMap,List.map_map,Function.comp_def] at HL
      exact (native_flatMap_cons_perm _ _ _).trans
        ((List.Perm.refl _).append ((List.flatMap_append_perm _ _ _).symm.trans
          (HL.append
            (native_flatMap_map_transpose _ _ NativeTwoHighPlacement.across))))
    | inr s=>
      have H:=ihV s star a
      unfold nativeHighOutsidePlacements nativeOutsideHighPlacements at H ⊢
      simp only [nativeHighMarkedRows,nativeOutsideMarkedRows,List.flatMap_map,
        List.flatMap_cons,List.flatMap_append]
      simp_rw [nativeOutsideRows_marked_right]
      simp_rw [List.map_cons,List.map_append,List.map_map,Function.comp_def,
        nativeHighRows_after_fresh,NativeTwoHighPlacement.ofTwo_fresh_commute,
        nativeHighRows_marked_right,nativeHighRows_marked_left_cross,
        List.map_map,Function.comp_def,NativeTwoHighPlacement.ofTwo_right,
        NativeTwoHighPlacement.swap_right,NativeTwoHighPlacement.ofTwo_across_reverse,
        NativeTwoHighPlacement.ofTwo_across]
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def]
      have HR:=H.map (NativeTwoHighPlacement.right T)
      simp only [List.map_flatMap,List.map_map,Function.comp_def] at HR
      exact (native_flatMap_cons_perm _ _ _).trans
        ((List.Perm.refl _).append ((List.flatMap_append_perm _ _ _).symm.trans
          ((native_flatMap_map_transpose _ _ (fun p r=>(NativeTwoHighPlacement.across r p).swap)).append HR)))

theorem native_high_outside_signed_placements_commute {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ) (F : NativeTwoHighPlacement T→ℝ) :
    ((nativeHighOutsidePlacements T s star a).map F).sum=
      ((nativeOutsideHighPlacements T s star a).map F).sum :=
  ((native_high_outside_placements_commute T s star a).map F).sum_eq

theorem native_high_outside_nested_signed_rows_commute {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(T.Slot→V.Slot)→V.Slot→V.Slot→ℝ) :
    ((nativeHighMarkedRows T s star a).map (fun p=>p.coeff*
      ((nativeOutsideMarkedRows p.tree (p.embed s) star a).map (fun r=>r.coeff*
        F r.tree (fun σ=>p.restrict (r.restrict σ)) (fun c=>r.embed (p.embed c))
          (r.embed p.mark) r.mark)).sum)).sum=
    ((nativeOutsideMarkedRows T s star a).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed s) star a).map (fun r=>r.coeff*
        F r.tree (fun σ=>p.restrict (r.restrict σ)) (fun c=>r.embed (p.embed c))
          r.mark (r.embed p.mark))).sum)).sum := by
  have H:=native_high_outside_signed_placements_commute T s star a
    (fun p=>p.coeff*F p.tree p.restrict p.embed p.markA p.markB)
  unfold nativeHighOutsidePlacements nativeOutsideHighPlacements at H
  rw [native_sum_map_flatMap,native_sum_map_flatMap] at H
  simp only [List.map_map,Function.comp_def,NativeTwoHighPlacement.ofTwo,NativeTwoHighPlacement.swap,
    mul_assoc,List.sum_map_mul_left] at H
  exact H

end OAI.SKFluctuations.Hierarchy.ClockTree
