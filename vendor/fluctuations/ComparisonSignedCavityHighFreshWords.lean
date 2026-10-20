module

public import ComparisonSignedCavityHighFreshDiagram

@[expose] public section

noncomputable section
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def NativeObservedDiagram.observe (D : NativeObservedDiagram T) (p : MarkedPlacement D.tree) :
    NativeObservedDiagram T where
  tree:=p.tree
  embed:=fun c=>p.embed (D.embed c)
  marks:=p.mark::D.marks.map p.embed
  read:=fun σ=>D.read (p.restrict σ)

def NativeObservedDiagram.fresh (D : NativeObservedDiagram T) (s : T.Slot) (star : ℕ) (a : ℝ) :
    NativeObservedDiagram T where
  tree:=(nativeFreshAtSlot D.tree a (D.embed s) star).tree
  embed:=fun c=>(nativeFreshAtSlot D.tree a (D.embed s) star).embed (D.embed c)
  marks:=D.marks.map (nativeFreshAtSlot D.tree a (D.embed s) star).embed++
    [(nativeFreshAtSlot D.tree a (D.embed s) star).mark]
  read:=fun σ=>D.read ((nativeFreshAtSlot D.tree a (D.embed s) star).restrict σ)

def NativeObservedDiagram.combineFresh (D : NativeObservedDiagram T)
    (E : NativeObservedDiagram D.tree) : NativeObservedDiagram T where
  tree:=E.tree
  embed:=fun c=>E.embed (D.embed c)
  marks:=E.marks.take 1++D.marks.map E.embed++E.marks.drop 1
  read:=fun σ=>D.read (E.read σ)

def nativeObservedHighRows (D : NativeObservedDiagram T) (s : T.Slot) (star : ℕ) (a : ℝ) :
    List (ℝ×NativeObservedDiagram T) :=
  (nativeHighMarkedRows D.tree (D.embed s) star a).map (fun p=>(p.coeff,D.observe p))

theorem native_observed_high_rows_fresh (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh aRow : ℝ) :
    nativeObservedHighRows (D.fresh s star aFresh) s star aRow=
      (nativeObservedHighRows D s star aRow).map (fun z=>(z.1,z.2.fresh s star aFresh)) := by
  have H:=native_high_fresh_diagram_rows D.tree (D.embed s) star hstar aFresh aRow
  unfold nativeObservedHighRows
  rw [List.map_map]
  apply (show ∀{l₁ l₂ : List (ℝ×NativeObservedDiagram T)},List.Forall₂ Eq l₁ l₂→l₁=l₂ from
    fun h=>by simpa only [List.forall₂_eq_eq_eq] using h)
  apply List.rel_map (fun p r h=>?_) H
  rcases h with ⟨hc,hd⟩
  apply Prod.ext hc
  have HH:=congrArg D.combineFresh hd
  simpa only [NativeObservedDiagram.combineFresh,nativeFreshHighDiagram,nativeHighFreshDiagram,
    NativeObservedDiagram.fresh,NativeObservedDiagram.observe,List.take_succ_cons,List.take_zero,
    List.drop_succ_cons,List.drop_zero,List.map_append,List.map_cons,List.map_nil,List.map_map,
    List.nil_append,List.cons_append,List.append_assoc,Function.comp_def] using HH

def nativeObservedHighWords (D : NativeObservedDiagram T) (s : T.Slot) (star : ℕ) :
    ℕ→List (ℝ×NativeObservedDiagram T)
  | 0=>[(1,D)]
  | k+1=>(nativeObservedHighRows D s star 0).flatMap (fun z=>
      (nativeObservedHighWords z.2 s star k).map (fun v=>(z.1*v.1,v.2)))

theorem native_observed_high_words_fresh (k : ℕ) (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh : ℝ) :
    nativeObservedHighWords (D.fresh s star aFresh) s star k=
      (nativeObservedHighWords D s star k).map (fun z=>(z.1,z.2.fresh s star aFresh)) := by
  induction k generalizing D with
  | zero=>rfl
  | succ k ih=>
    simp only [nativeObservedHighWords,native_observed_high_rows_fresh D s star hstar aFresh,
      List.flatMap_map,List.map_flatMap]
    apply congrArg (fun F=>(nativeObservedHighRows D s star 0).flatMap F)
    funext z
    rw [ih z.2]
    simp only [List.map_map,Function.comp_def]

end OAI.SKFluctuations.Hierarchy.ClockTree
