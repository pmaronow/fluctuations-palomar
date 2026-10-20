module

public import ComparisonSignedCavitySecondLowLabeledHighWordCommutation
public import CavityCutBlocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowOriginalLabelOrder (j : Fin 8) : List (Fin 4) :=
  match j.val with
  | 0 => [0,1,2,3]
  | 1 => [0,1,3,2]
  | 2 => [1,0,2,3]
  | 3 => [1,0,3,2]
  | 4 => [1,3,0,2]
  | 5 => [3,1,0,2]
  | 6 => [1,3,2,0]
  | _ => [3,1,2,0]

theorem native_second_low_eight_labeled_endpoint_routing
    (D : NativeSecondLowLabeledDiagram T) (hD : D.preservesOldSplits)
    (targets : Fin 4 → T.Slot) (high : ℕ)
    (hmid : targets 1 = targets 2)
    (hA : T.splitIndex (targets 0) (targets 1) ≤ high)
    (hB : T.splitIndex (targets 3) (targets 1) ≤ high)
    (hAB : T.splitIndex (targets 0) (targets 3) ≤ high) (j : Fin 8) :
    (nativeSecondLowLabeledHighWord D targets high (nativeSecondLowOriginalLabelOrder j)).Perm
      (nativeSecondLowLabeledHighWord D targets high [0,3,1,2]) := by
  have hA2 : T.splitIndex (targets 0) (targets 2) ≤ high := hmid ▸ hA
  have h2B : T.splitIndex (targets 2) (targets 3) ≤ high := by
    rw [T.splitIndex_symm,hmid.symm]
    exact hB
  have h1B : T.splitIndex (targets 1) (targets 3) ≤ high := by
    rw [T.splitIndex_symm]
    exact hB
  have h1A : T.splitIndex (targets 1) (targets 0) ≤ high := by
    rw [T.splitIndex_symm]
    exact hA
  have h2A : T.splitIndex (targets 2) (targets 0) ≤ high := by
    rw [T.splitIndex_symm]
    exact hA2
  have hBA : T.splitIndex (targets 3) (targets 0) ≤ high := by
    rw [T.splitIndex_symm]
    exact hAB
  have H0 : (nativeSecondLowLabeledHighWord D targets high [0,1,2,3]).Perm
      (nativeSecondLowLabeledHighWord D targets high [0,3,1,2]) :=
    (native_second_low_labeled_high_word_adjacent_swap D hD targets high [0,1] [] 2 3 (by decide) h2B).trans
      (native_second_low_labeled_high_word_adjacent_swap D hD targets high [0] [2] 1 3 (by decide) h1B)
  have H1 : (nativeSecondLowLabeledHighWord D targets high [0,1,3,2]).Perm
      (nativeSecondLowLabeledHighWord D targets high [0,3,1,2]) :=
    native_second_low_labeled_high_word_adjacent_swap D hD targets high [0] [2] 1 3 (by decide) h1B
  have H4 : (nativeSecondLowLabeledHighWord D targets high [1,3,0,2]).Perm
      (nativeSecondLowLabeledHighWord D targets high [0,3,1,2]) :=
    (native_second_low_labeled_high_word_adjacent_swap D hD targets high [] [0,2] 1 3 (by decide) h1B).trans
      ((native_second_low_labeled_high_word_adjacent_swap D hD targets high [3] [2] 1 0 (by decide) h1A).trans
        (native_second_low_labeled_high_word_adjacent_swap D hD targets high [] [1,2] 3 0 (by decide) hBA))
  have H5 : (nativeSecondLowLabeledHighWord D targets high [3,1,0,2]).Perm
      (nativeSecondLowLabeledHighWord D targets high [0,3,1,2]) :=
    (native_second_low_labeled_high_word_adjacent_swap D hD targets high [3] [2] 1 0 (by decide) h1A).trans
      (native_second_low_labeled_high_word_adjacent_swap D hD targets high [] [1,2] 3 0 (by decide) hBA)
  fin_cases j
  all_goals dsimp only [nativeSecondLowOriginalLabelOrder]
  · exact H0
  · exact H1
  · exact (native_second_low_labeled_high_word_adjacent_swap D hD targets high [] [2,3] 1 0 (by decide) h1A).trans H0
  · exact (native_second_low_labeled_high_word_adjacent_swap D hD targets high [] [3,2] 1 0 (by decide) h1A).trans H1
  · exact H4
  · exact H5
  · exact (native_second_low_labeled_high_word_adjacent_swap D hD targets high [1,3] [] 2 0 (by decide) h2A).trans H4
  · exact (native_second_low_labeled_high_word_adjacent_swap D hD targets high [3,1] [] 2 0 (by decide) h2A).trans H5

end OAI.SKFluctuations.Hierarchy.ClockTree
