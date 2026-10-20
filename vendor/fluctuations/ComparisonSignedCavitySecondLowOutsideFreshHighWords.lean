module

public import ComparisonSignedCavitySecondLowOutsideFreshHighDiagram
public import ComparisonSignedCavityHighFreshWords

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem native_second_low_observed_high_rows_fresh_any (D : NativeObservedDiagram T)
    (b c : T.Slot) (star high : ℕ) (hstar : star≤as.length) (hhigh : star≤high)
    (aFresh aRow : ℝ) :
    nativeObservedHighRows (D.fresh b star aFresh) c high aRow=
      (nativeObservedHighRows D c high aRow).map (fun z=>(z.1,z.2.fresh b star aFresh)) := by
  have H:=native_second_low_outside_fresh_high_diagram_rows D.tree (D.embed b) (D.embed c)
    star high hstar hhigh aFresh aRow
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

def nativeSecondLowObservedHighWord (D : NativeObservedDiagram T) (high : ℕ) :
    List T.Slot→List (ℝ×NativeObservedDiagram T)
  | []=>[(1,D)]
  | c::cs=>(nativeObservedHighRows D c high 0).flatMap (fun z=>
      (nativeSecondLowObservedHighWord z.2 high cs).map (fun v=>(z.1*v.1,v.2)))

theorem native_second_low_observed_high_word_fresh_any (cs : List T.Slot)
    (D : NativeObservedDiagram T) (b : T.Slot) (star high : ℕ)
    (hstar : star≤as.length) (hhigh : star≤high) (aFresh : ℝ) :
    nativeSecondLowObservedHighWord (D.fresh b star aFresh) high cs=
      (nativeSecondLowObservedHighWord D high cs).map (fun z=>(z.1,z.2.fresh b star aFresh)) := by
  induction cs generalizing D with
  | nil=>rfl
  | cons c cs ih=>
    simp only [nativeSecondLowObservedHighWord,
      native_second_low_observed_high_rows_fresh_any D b c star high hstar hhigh aFresh,
      List.flatMap_map,List.map_flatMap]
    apply congrArg (fun F=>(nativeObservedHighRows D c high 0).flatMap F)
    funext z
    rw [ih z.2]
    simp only [List.map_map,Function.comp_def]

end OAI.SKFluctuations.Hierarchy.ClockTree
