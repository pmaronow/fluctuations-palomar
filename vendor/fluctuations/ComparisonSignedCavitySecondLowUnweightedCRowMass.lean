module

public import ComparisonSignedCavityHighMarkedRows

@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
namespace OAI.SKFluctuations.Hierarchy.ClockTree

 theorem native_marked_clock_row_mass {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) :
    ((T.markedAttach a).map (fun p=>p.coeff)).sum=a := by
  induction T generalizing a with
  | leaf=>simp only [markedAttach,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      MarkedPlacement.coincide,MarkedPlacement.fresh];ring
  | step b T ih=>
    simp only [markedAttach,List.map_cons,List.map_map,Function.comp_def,List.sum_cons,
      MarkedPlacement.fresh,MarkedPlacement.step,ih]
    ring
  | fork T V ihT ihV=>
    simp only [markedAttach,List.map_cons,List.map_append,List.map_map,Function.comp_def,
      List.sum_cons,List.sum_append,MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,ihT,ihV]
    ring

 theorem native_high_marked_clock_row_mass {S : Type} {as : List PositiveMass}
    (T : ClockTree S as) (c : T.Slot) (star : ℕ) (a : ℝ) (hcut : star+1≤as.length) :
    ((nativeHighMarkedRows T c star a).map (fun p=>p.coeff)).sum=
      partitionPoint a as (star+1) := by
  induction T generalizing star a with
  | leaf=>simp only [List.length_nil] at hcut;omega
  | step b T ih=>
    cases star with
    | zero=>
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def,MarkedPlacement.step,
        native_marked_clock_row_mass,partitionPoint,partitionValues]
      exact (partitionValues_zero id b.val _).symm
    | succ star=>
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def,MarkedPlacement.step]
      have H:=ih c star b.val (by simp only [List.length_cons] at hcut;omega)
      simpa only [partitionPoint,partitionValues,Nat.add_assoc] using H
  | fork T V ihT ihV=>
    cases c with
    | inl c=>
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def,MarkedPlacement.left]
      exact ihT c star a hcut
    | inr c=>
      simp only [nativeHighMarkedRows,List.map_map,Function.comp_def,MarkedPlacement.right]
      exact ihV c star a hcut

end OAI.SKFluctuations.Hierarchy.ClockTree
