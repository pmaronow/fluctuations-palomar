module

public import ComparisonSignedCavityHighRowsCommutation
public import ComparisonSignedCavityHighOutsideCommutation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

structure NativeSecondLowLabeledDiagram (T : ClockTree S as) where
  tree : ClockTree S as
  embed : T.Slot→tree.Slot
  read : tree.Assignment→T.Assignment
  marks : Fin 4→tree.Slot

namespace NativeSecondLowLabeledDiagram

def base (T : ClockTree S as) (a : T.Slot) : NativeSecondLowLabeledDiagram T where
  tree:=T
  embed:=id
  read:=id
  marks:=fun _=>a

def observe (D : NativeSecondLowLabeledDiagram T) (i : Fin 4) (p : MarkedPlacement D.tree) :
    NativeSecondLowLabeledDiagram T where
  tree:=p.tree
  embed:=fun c=>p.embed (D.embed c)
  read:=fun σ=>D.read (p.restrict σ)
  marks:=fun k=>if k=i then p.mark else p.embed (D.marks k)

def attachTwo (D : NativeSecondLowLabeledDiagram T) (i j : Fin 4) (P : NativeTwoHighPlacement D.tree) :
    NativeSecondLowLabeledDiagram T where
  tree:=P.tree
  embed:=fun c=>P.embed (D.embed c)
  read:=fun σ=>D.read (P.restrict σ)
  marks:=fun k=>if k=i then P.markA else if k=j then P.markB else P.embed (D.marks k)

theorem observe_observe (D : NativeSecondLowLabeledDiagram T) (i j : Fin 4) (hij : i≠j)
    (p : MarkedPlacement D.tree) (r : MarkedPlacement p.tree) :
    (D.observe i p).observe j r=D.attachTwo i j (NativeTwoHighPlacement.ofTwo p r) := by
  unfold observe attachTwo NativeTwoHighPlacement.ofTwo
  congr 1
  funext k
  by_cases Hi : k=i <;> by_cases Hj : k=j <;> simp_all

theorem attachTwo_swap (D : NativeSecondLowLabeledDiagram T) (i j : Fin 4) (hij : i≠j)
    (P : NativeTwoHighPlacement D.tree) :
    D.attachTwo i j P.swap=D.attachTwo j i P := by
  unfold attachTwo NativeTwoHighPlacement.swap
  congr 1
  funext k
  by_cases Hi : k=i <;> by_cases Hj : k=j <;> simp_all

def preservesOldSplits (D : NativeSecondLowLabeledDiagram T) : Prop :=
  ∀c d:T.Slot,D.tree.splitIndex (D.embed c) (D.embed d)=T.splitIndex c d

theorem base_preserves (a : T.Slot) : (base T a).preservesOldSplits := fun _ _=>rfl

theorem observe_preserves (D : NativeSecondLowLabeledDiagram T) (hD : D.preservesOldSplits)
    (i : Fin 4) (p : MarkedPlacement D.tree) (hp : p∈D.tree.markedAttach 0) :
    (D.observe i p).preservesOldSplits := by
  intro c d
  exact ((D.tree.markedAttach_embed_preserves 0 p hp).2 (D.embed c) (D.embed d)).trans (hD c d)

end NativeSecondLowLabeledDiagram

def nativeSecondLowLabeledHighRows (D : NativeSecondLowLabeledDiagram T)
    (targets : Fin 4→T.Slot) (high : ℕ) (i : Fin 4) : List (ℝ×NativeSecondLowLabeledDiagram T) :=
  (nativeHighMarkedRows D.tree (D.embed (targets i)) high 0).map (fun p=>(p.coeff,D.observe i p))

def nativeSecondLowLabeledHighWord (D : NativeSecondLowLabeledDiagram T)
    (targets : Fin 4→T.Slot) (high : ℕ) : List (Fin 4)→List (ℝ×NativeSecondLowLabeledDiagram T)
  | []=>[(1,D)]
  | i::is=>(nativeSecondLowLabeledHighRows D targets high i).flatMap (fun z=>
      (nativeSecondLowLabeledHighWord z.2 targets high is).map (fun v=>(z.1*v.1,v.2)))

theorem native_second_low_labeled_two_high_word_eq (D : NativeSecondLowLabeledDiagram T)
    (targets : Fin 4→T.Slot) (high : ℕ) (i j : Fin 4) (hij : i≠j) :
    nativeSecondLowLabeledHighWord D targets high [i,j]=
      (nativeTwoHighPlacements D.tree (D.embed (targets i)) (D.embed (targets j)) high 0).map
        (fun P=>(P.coeff,D.attachTwo i j P)) := by
  simp only [nativeSecondLowLabeledHighWord,nativeSecondLowLabeledHighRows,nativeTwoHighPlacements,
    List.flatMap_map,List.map_cons,List.map_nil,mul_one]
  simp_rw [NativeSecondLowLabeledDiagram.observe_observe D i j hij]
  simp only [native_flatMap_singleton_map,List.map_flatMap,List.map_map,Function.comp_def,
    NativeSecondLowLabeledDiagram.observe,NativeTwoHighPlacement.ofTwo]

theorem native_second_low_labeled_two_high_words_commute (D : NativeSecondLowLabeledDiagram T)
    (targets : Fin 4→T.Slot) (high : ℕ) (i j : Fin 4) (hij : i≠j)
    (hcross : D.tree.splitIndex (D.embed (targets i)) (D.embed (targets j))≤high) :
    (nativeSecondLowLabeledHighWord D targets high [i,j]).Perm
      (nativeSecondLowLabeledHighWord D targets high [j,i]) := by
  rw [native_second_low_labeled_two_high_word_eq D targets high i j hij,
    native_second_low_labeled_two_high_word_eq D targets high j i hij.symm]
  have H:=(native_two_high_placements_commute D.tree (D.embed (targets i)) (D.embed (targets j))
    high 0 hcross).map (fun P=>(P.coeff,D.attachTwo i j P))
  have Hcoeff (P : NativeTwoHighPlacement D.tree) : P.swap.coeff=P.coeff:=rfl
  simpa only [List.map_map,Function.comp_def,Hcoeff,
    NativeSecondLowLabeledDiagram.attachTwo_swap D i j hij] using H

theorem native_second_low_labeled_high_word_append (D : NativeSecondLowLabeledDiagram T)
    (targets : Fin 4→T.Slot) (high : ℕ) (xs ys : List (Fin 4)) :
    nativeSecondLowLabeledHighWord D targets high (xs++ys)=
      (nativeSecondLowLabeledHighWord D targets high xs).flatMap (fun z=>
        (nativeSecondLowLabeledHighWord z.2 targets high ys).map (fun v=>(z.1*v.1,v.2))) := by
  induction xs generalizing D with
  | nil=>simp only [List.nil_append,nativeSecondLowLabeledHighWord,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,one_mul,Prod.mk.eta,List.map_id']
  | cons i xs ih=>
    simp only [List.cons_append,nativeSecondLowLabeledHighWord,ih,List.flatMap_assoc,
      List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def,mul_assoc]

theorem native_second_low_labeled_high_word_adjacent_swap (D : NativeSecondLowLabeledDiagram T)
    (hD : D.preservesOldSplits) (targets : Fin 4→T.Slot) (high : ℕ)
    (xs ys : List (Fin 4)) (i j : Fin 4) (hij : i≠j) (hcross : T.splitIndex (targets i) (targets j)≤high) :
    (nativeSecondLowLabeledHighWord D targets high (xs++i::j::ys)).Perm
      (nativeSecondLowLabeledHighWord D targets high (xs++j::i::ys)) := by
  induction xs generalizing D with
  | nil=>
    change (nativeSecondLowLabeledHighWord D targets high ([i,j]++ys)).Perm
      (nativeSecondLowLabeledHighWord D targets high ([j,i]++ys))
    rw [native_second_low_labeled_high_word_append,native_second_low_labeled_high_word_append]
    exact (native_second_low_labeled_two_high_words_commute D targets high i j hij
      (by rw [hD];exact hcross)).flatMap_right _
  | cons k xs ih=>
    simp only [List.cons_append,nativeSecondLowLabeledHighWord]
    apply List.Perm.flatMap_left
    intro z hz
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hz
    have Hmarked : p∈D.tree.markedAttach 0:=(mem_nativeHighMarkedRows D.tree
      (D.embed (targets k)) high 0 p).mp hp |>.1
    exact (ih (D.observe k p) (D.observe_preserves hD k p Hmarked)).map (fun v=>(p.coeff*v.1,v.2))

end OAI.SKFluctuations.Hierarchy.ClockTree
