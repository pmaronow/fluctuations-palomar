module

public import ComparisonSignedCavityHighMarkedRows
public import Mathlib.Data.List.Perm.Basic

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

structure NativeTwoHighPlacement {as : List PositiveMass} (T : ClockTree S as) where
  tree : ClockTree S as
  coeff : ℝ
  restrict : tree.Assignment→T.Assignment
  embed : T.Slot→tree.Slot
  markA : tree.Slot
  markB : tree.Slot

namespace NativeTwoHighPlacement

def ofTwo {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) : NativeTwoHighPlacement T where
  tree:=r.tree
  coeff:=p.coeff*r.coeff
  restrict:=fun σ=>p.restrict (r.restrict σ)
  embed:=fun c=>r.embed (p.embed c)
  markA:=r.embed p.mark
  markB:=r.mark

def swap {as : List PositiveMass} {T : ClockTree S as}
    (p : NativeTwoHighPlacement T) : NativeTwoHighPlacement T :=
  {p with markA:=p.markB,markB:=p.markA}

def step {as : List PositiveMass} {T : ClockTree S as}
    (b : PositiveMass) (p : NativeTwoHighPlacement T) : NativeTwoHighPlacement (T.step b) where
  tree:=p.tree.step b
  coeff:=p.coeff
  restrict:=p.restrict
  embed:=p.embed
  markA:=p.markA
  markB:=p.markB

def left {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : NativeTwoHighPlacement T) : NativeTwoHighPlacement (T.fork V) where
  tree:=p.tree.fork V
  coeff:=p.coeff
  restrict:=fun σ=>(p.restrict σ.1,σ.2)
  embed:=Sum.map p.embed id
  markA:=Sum.inl p.markA
  markB:=Sum.inl p.markB

def right {as : List PositiveMass} (T : ClockTree S as) {V : ClockTree S as}
    (p : NativeTwoHighPlacement V) : NativeTwoHighPlacement (T.fork V) where
  tree:=T.fork p.tree
  coeff:=p.coeff
  restrict:=fun σ=>(σ.1,p.restrict σ.2)
  embed:=Sum.map id p.embed
  markA:=Sum.inr p.markA
  markB:=Sum.inr p.markB

def across {as : List PositiveMass} {T V : ClockTree S as}
    (p : MarkedPlacement T) (r : MarkedPlacement V) : NativeTwoHighPlacement (T.fork V) where
  tree:=p.tree.fork r.tree
  coeff:=p.coeff*r.coeff
  restrict:=fun σ=>(p.restrict σ.1,r.restrict σ.2)
  embed:=Sum.map p.embed r.embed
  markA:=Sum.inl p.mark
  markB:=Sum.inr r.mark

theorem ofTwo_step {as : List PositiveMass} {T : ClockTree S as}
    (b : PositiveMass) (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    ofTwo (p.step b) (r.step b)=step b (ofTwo p r) := rfl

theorem ofTwo_left {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    ofTwo (p.left V) (r.left V)=left V (ofTwo p r) := by
  unfold ofTwo left MarkedPlacement.left
  congr 1
  funext c
  cases c <;> rfl

theorem ofTwo_right {as : List PositiveMass} (T : ClockTree S as) {V : ClockTree S as}
    (p : MarkedPlacement V) (r : MarkedPlacement p.tree) :
    ofTwo (p.right T) (r.right T)=right T (ofTwo p r) := by
  unfold ofTwo right MarkedPlacement.right
  congr 1
  funext c
  cases c <;> rfl

theorem ofTwo_across {as : List PositiveMass} {T V : ClockTree S as}
    (p : MarkedPlacement T) (r : MarkedPlacement V) :
    ofTwo (p.left V) (r.right p.tree)=across p r := by
  unfold ofTwo across MarkedPlacement.left MarkedPlacement.right
  congr 1
  funext c
  cases c <;> rfl

theorem ofTwo_across_swapped {as : List PositiveMass} {T V : ClockTree S as}
    (p : MarkedPlacement T) (r : MarkedPlacement V) :
    (ofTwo (r.right T) (p.left r.tree)).swap=across p r := by
  unfold ofTwo swap across MarkedPlacement.left MarkedPlacement.right
  congr 1
  · ring
  · funext c
    cases c <;> rfl

theorem swap_step {as : List PositiveMass} {T : ClockTree S as}
    (b : PositiveMass) (p : NativeTwoHighPlacement T) :
    (step b p).swap=step b p.swap := rfl

theorem swap_left {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : NativeTwoHighPlacement T) :
    (left V p).swap=left V p.swap := rfl

theorem swap_right {as : List PositiveMass} (T : ClockTree S as) {V : ClockTree S as}
    (p : NativeTwoHighPlacement V) :
    (right T p).swap=right T p.swap := rfl

theorem swap_swap {as : List PositiveMass} {T : ClockTree S as}
    (p : NativeTwoHighPlacement T) : p.swap.swap=p := rfl

theorem ofTwo_across_reverse {as : List PositiveMass} {T V : ClockTree S as}
    (p : MarkedPlacement T) (r : MarkedPlacement V) :
    ofTwo (r.right T) (p.left r.tree)=(across p r).swap := by
  have H:=congrArg swap (ofTwo_across_swapped p r)
  simpa only [swap_swap] using H

end NativeTwoHighPlacement

theorem nativeHighRows_marked_step {as : List PositiveMass} {T : ClockTree S as}
    (m : PositiveMass) (p : MarkedPlacement T) (c : T.Slot) (star : ℕ) (aRow : ℝ) :
    nativeHighMarkedRows (p.step m).tree ((p.step m).embed c) (star+1) aRow=
      (nativeHighMarkedRows p.tree (p.embed c) star m.val).map (fun r=>r.step m) := rfl

theorem nativeHighRows_marked_left {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : MarkedPlacement T) (c : T.Slot) (star : ℕ) (aRow : ℝ) :
    nativeHighMarkedRows (p.left V).tree ((p.left V).embed (Sum.inl c)) star aRow=
      (nativeHighMarkedRows p.tree (p.embed c) star aRow).map (fun r=>r.left V) := rfl

theorem nativeHighRows_marked_right {as : List PositiveMass} (T : ClockTree S as)
    {V : ClockTree S as} (p : MarkedPlacement V) (c : V.Slot) (star : ℕ) (aRow : ℝ) :
    nativeHighMarkedRows (p.right T).tree ((p.right T).embed (Sum.inr c)) star aRow=
      (nativeHighMarkedRows p.tree (p.embed c) star aRow).map (fun r=>r.right T) := rfl

theorem nativeHighRows_marked_left_cross {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : MarkedPlacement T) (c : V.Slot) (star : ℕ) (aRow : ℝ) :
    nativeHighMarkedRows (p.left V).tree ((p.left V).embed (Sum.inr c)) star aRow=
      (nativeHighMarkedRows V c star aRow).map (fun r=>r.right p.tree) := rfl

theorem nativeHighRows_marked_right_cross {as : List PositiveMass} (T : ClockTree S as)
    {V : ClockTree S as} (p : MarkedPlacement V) (c : T.Slot) (star : ℕ) (aRow : ℝ) :
    nativeHighMarkedRows (p.right T).tree ((p.right T).embed (Sum.inl c)) star aRow=
      (nativeHighMarkedRows T c star aRow).map (fun r=>r.left p.tree) := rfl

def nativeTwoHighPlacements {as : List PositiveMass} (T : ClockTree S as)
    (a b : T.Slot) (star : ℕ) (aRow : ℝ) : List (NativeTwoHighPlacement T) :=
  (nativeHighMarkedRows T a star aRow).flatMap fun p=>
    (nativeHighMarkedRows p.tree (p.embed b) star aRow).map (NativeTwoHighPlacement.ofTwo p)

theorem native_flatMap_map_transpose {A B C : Type}
    (l : List A) (r : List B) (f : A→B→C) :
    (l.flatMap fun a=>r.map (f a)).Perm (r.flatMap fun b=>l.map fun a=>f a b) := by
  induction l with
  | nil=>simp
  | cons a l ih=>
    simp only [List.flatMap_cons,List.map_cons]
    exact (List.Perm.refl _ |>.append ih).trans
      (List.map_append_flatMap_perm r (f a) (fun b=>l.map fun a=>f a b))

theorem native_two_high_placements_commute {as : List PositiveMass}
    (T : ClockTree S as) (a b : T.Slot) (star : ℕ) (aRow : ℝ)
    (hab : T.splitIndex a b ≤ star) :
    (nativeTwoHighPlacements T a b star aRow).Perm
      ((nativeTwoHighPlacements T b a star aRow).map NativeTwoHighPlacement.swap) := by
  induction T generalizing star aRow with
  | leaf=>simp [nativeTwoHighPlacements,nativeHighMarkedRows]
  | @step m tail T ih=>
    cases star with
    | zero=>change 1+T.splitIndex a b ≤ 0 at hab;omega
    | succ star=>
      have H:=ih a b star m.val (by change 1+T.splitIndex a b ≤ star+1 at hab;omega)
      simp only [nativeTwoHighPlacements,nativeHighMarkedRows,List.flatMap_map,List.map_flatMap]
      simp_rw [nativeHighRows_marked_step,List.map_map,Function.comp_def,
        NativeTwoHighPlacement.ofTwo_step,NativeTwoHighPlacement.swap_step]
      simpa only [nativeTwoHighPlacements,List.map_flatMap,List.map_map,Function.comp_def] using
        H.map (NativeTwoHighPlacement.step m)
  | @fork tail T V ihT ihV=>
    cases a with
    | inl a=>
      cases b with
      | inl b=>
        have H:=ihT a b star aRow hab
        simp only [nativeTwoHighPlacements,nativeHighMarkedRows,List.flatMap_map,List.map_flatMap]
        simp_rw [nativeHighRows_marked_left,List.map_map,Function.comp_def,
          NativeTwoHighPlacement.ofTwo_left,NativeTwoHighPlacement.swap_left]
        simpa only [nativeTwoHighPlacements,List.map_flatMap,List.map_map,Function.comp_def] using
          H.map (NativeTwoHighPlacement.left V)
      | inr b=>
        simp only [nativeTwoHighPlacements,nativeHighMarkedRows,List.flatMap_map,List.map_flatMap]
        simp_rw [nativeHighRows_marked_left_cross,nativeHighRows_marked_right_cross,
          List.map_map,Function.comp_def,NativeTwoHighPlacement.ofTwo_across,
          NativeTwoHighPlacement.ofTwo_across_swapped]
        exact native_flatMap_map_transpose (nativeHighMarkedRows T a star aRow)
          (nativeHighMarkedRows V b star aRow) NativeTwoHighPlacement.across
    | inr a=>
      cases b with
      | inl b=>
        simp only [nativeTwoHighPlacements,nativeHighMarkedRows,List.flatMap_map,List.map_flatMap]
        simp_rw [nativeHighRows_marked_left_cross,nativeHighRows_marked_right_cross,
          List.map_map,Function.comp_def,NativeTwoHighPlacement.ofTwo_across,
          NativeTwoHighPlacement.ofTwo_across_reverse]
        exact native_flatMap_map_transpose (nativeHighMarkedRows V a star aRow)
          (nativeHighMarkedRows T b star aRow)
          (fun p r=>(NativeTwoHighPlacement.across r p).swap)
      | inr b=>
        have H:=ihV a b star aRow hab
        simp only [nativeTwoHighPlacements,nativeHighMarkedRows,List.flatMap_map,List.map_flatMap]
        simp_rw [nativeHighRows_marked_right,List.map_map,Function.comp_def,
          NativeTwoHighPlacement.ofTwo_right,NativeTwoHighPlacement.swap_right]
        simpa only [nativeTwoHighPlacements,List.map_flatMap,List.map_map,Function.comp_def] using
          H.map (NativeTwoHighPlacement.right T)

theorem native_two_high_signed_placements_commute {as : List PositiveMass}
    (T : ClockTree S as) (a b : T.Slot) (star : ℕ) (aRow : ℝ)
    (hab : T.splitIndex a b ≤ star) (F : NativeTwoHighPlacement T→ℝ) :
    ((nativeTwoHighPlacements T a b star aRow).map F).sum=
      ((nativeTwoHighPlacements T b a star aRow).map (fun p=>F p.swap)).sum := by
  have H:=(native_two_high_placements_commute T a b star aRow hab).map F
  simpa only [List.map_map,Function.comp_def] using H.sum_eq

end OAI.SKFluctuations.Hierarchy.ClockTree
