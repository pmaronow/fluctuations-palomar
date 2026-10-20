module

public import ComparisonSignedCavityHighRowsCommutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

def nativeOutsideMarkedRows : {as : List PositiveMass}→(T : ClockTree S as)→
    T.Slot→ℕ→ℝ→List (MarkedPlacement T)
  | _,.leaf,_,_,a=>ClockTree.leaf.markedAttach a
  | _,.step b T,_,0,a=>[MarkedPlacement.fresh (T.step b) (a-b.val)]
  | _,.step b T,s,star+1,a=>MarkedPlacement.fresh (T.step b) (a-b.val)::
      (nativeOutsideMarkedRows T s star b.val).map (fun p=>p.step b)
  | _,.fork T V,s,star,a=>match (s:T.Slot⊕V.Slot) with
    | Sum.inl s=>MarkedPlacement.fresh (T.fork V) (-a)::
        ((nativeOutsideMarkedRows T s star a).map (fun p=>p.left V)++
         (V.markedAttach a).map (fun p=>p.right T))
    | Sum.inr s=>MarkedPlacement.fresh (T.fork V) (-a)::
        ((T.markedAttach a).map (fun p=>p.left V)++
         (nativeOutsideMarkedRows V s star a).map (fun p=>p.right T))

theorem nativeOutsideMarkedRows_eq_filter {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ) :
    nativeOutsideMarkedRows T s star a=
      (T.markedAttach a).filter (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark ≤ star)) := by
  induction T generalizing star a with
  | leaf=>
    simp [nativeOutsideMarkedRows,markedAttach,MarkedPlacement.fresh,MarkedPlacement.coincide,splitIndex]
  | step b T ih=>
    cases star with
    | zero=>
      simp [nativeOutsideMarkedRows,markedAttach,MarkedPlacement.fresh,MarkedPlacement.step,
        splitIndex,List.filter_map,Function.comp_def]
    | succ star=>
      rw [nativeOutsideMarkedRows,ih]
      simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.step,splitIndex,
        List.filter_map,Function.comp_def]
      simp only [Nat.add_comm 1,Nat.add_le_add_iff_right]
      rfl
  | fork T V ihT ihV=>
    cases s with
    | inl s=>
      rw [nativeOutsideMarkedRows,ihT]
      simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        splitIndex,List.filter_map,Function.comp_def]
      rfl
    | inr s=>
      rw [nativeOutsideMarkedRows,ihV]
      simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,
        splitIndex,List.filter_map,Function.comp_def]
      rfl

theorem mem_nativeOutsideMarkedRows {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (star : ℕ) (a : ℝ) (p : MarkedPlacement T) :
    p∈nativeOutsideMarkedRows T s star a ↔
      p∈T.markedAttach a ∧ p.tree.splitIndex (p.embed s) p.mark ≤ star := by
  rw [nativeOutsideMarkedRows_eq_filter]
  simp only [List.mem_filter,decide_eq_true_eq]

end OAI.SKFluctuations.Hierarchy.ClockTree
