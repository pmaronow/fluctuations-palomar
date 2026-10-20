module

public import ComparisonSignedCavityHighFreshWords
public import ComparisonSignedCavityActualResourceFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}

def NativeObservedDiagram.identity (T : ClockTree S as) : NativeObservedDiagram T where
  tree:=T
  embed:=id
  marks:=[]
  read:=id

def nativeObservedHighWordSum (D : NativeObservedDiagram T) (s : T.Slot)
    (star k : ℕ) (F : NativeObservedDiagram T→ℝ) : ℝ :=
  ((nativeObservedHighWords D s star k).map (fun z=>z.1*F z.2)).sum

theorem native_observed_high_word_sum_fresh (k : ℕ) (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh : ℝ)
    (F : NativeObservedDiagram T→ℝ) :
    nativeObservedHighWordSum (D.fresh s star aFresh) s star k F=
      nativeObservedHighWordSum D s star k (fun E=>F (E.fresh s star aFresh)) := by
  unfold nativeObservedHighWordSum
  rw [native_observed_high_words_fresh k D s star hstar aFresh,List.map_map]
  rfl

theorem native_observed_high_word_sum_succ (D : NativeObservedDiagram T)
    (s : T.Slot) (star k : ℕ) (F : NativeObservedDiagram T→ℝ) :
    nativeObservedHighWordSum D s star (k+1) F=
      ((nativeHighMarkedRows D.tree (D.embed s) star 0).map (fun p=>p.coeff*
        nativeObservedHighWordSum (D.observe p) s star k F)).sum := by
  unfold nativeObservedHighWordSum
  simp only [nativeObservedHighWords,nativeObservedHighRows,List.flatMap_map,List.map_flatMap,
    native_sum_flatMap,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro z _
  ring

theorem native_observed_high_word_sum_zero (D : NativeObservedDiagram T)
    (s : T.Slot) (star : ℕ) (F : NativeObservedDiagram T→ℝ) :
    nativeObservedHighWordSum D s star 0 F=F D := by
  simp only [nativeObservedHighWordSum,nativeObservedHighWords,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,one_mul,add_zero]

end OAI.SKFluctuations.Hierarchy.ClockTree
