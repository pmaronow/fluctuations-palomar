module

public import ComparisonSignedCavityFreshGraft

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

def nativeHighMarkedRows : {as : List PositiveMass} → (T : ClockTree S as) →
    T.Slot → ℕ → ℝ → List (MarkedPlacement T)
  | _,.leaf,_,_,_=>[]
  | _,.step b T,s,0,_=>(T.markedAttach b.val).map (fun p=>p.step b)
  | _,.step b T,s,star+1,_=>(nativeHighMarkedRows T s star b.val).map (fun p=>p.step b)
  | _,.fork T V,s,star,a=>match (s:T.Slot⊕V.Slot) with
    | Sum.inl s=>(nativeHighMarkedRows T s star a).map (fun p=>p.left V)
    | Sum.inr s=>(nativeHighMarkedRows V s star a).map (fun p=>p.right T)

theorem nativeHighMarkedRows_eq_filter {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ) :
    nativeHighMarkedRows T s star a=
      (T.markedAttach a).filter (fun p=>decide (star<p.tree.splitIndex (p.embed s) p.mark)) := by
  induction T generalizing star a with
  | leaf=>
    simp [nativeHighMarkedRows,markedAttach,MarkedPlacement.fresh,MarkedPlacement.coincide,splitIndex]
  | step b T ih=>
    cases star with
    | zero=>
      simp [nativeHighMarkedRows,markedAttach,MarkedPlacement.fresh,MarkedPlacement.step,
        splitIndex,List.filter_map,Function.comp_def]
    | succ star=>
      rw [nativeHighMarkedRows,ih]
      simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.step,splitIndex,
        List.filter_map,Function.comp_def,Nat.add_comm]
      simp only [Nat.add_comm 1,Nat.add_lt_add_iff_right]
      rfl
  | fork T V ihT ihV=>
    cases s with
    | inl s=>
      rw [nativeHighMarkedRows,ihT]
      simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        splitIndex,List.filter_map,Function.comp_def]
    | inr s=>
      rw [nativeHighMarkedRows,ihV]
      simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        splitIndex,List.filter_map,Function.comp_def]

theorem mem_nativeHighMarkedRows {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ) (p : MarkedPlacement T) :
    p∈nativeHighMarkedRows T s star a ↔
      p∈T.markedAttach a ∧ star<p.tree.splitIndex (p.embed s) p.mark := by
  rw [nativeHighMarkedRows_eq_filter]
  simp only [List.mem_filter,decide_eq_true_eq]

end OAI.SKFluctuations.Hierarchy.ClockTree
