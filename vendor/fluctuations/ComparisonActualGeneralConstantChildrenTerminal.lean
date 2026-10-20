module

public import ComparisonActualGeneralConstantJointFourReadout
public import ComparisonSignedCavityActualConstantSourceChildrenTerminalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization Set
open scoped NNReal Topology BigOperators
set_option maxHeartbeats 16000000

theorem actual_general_constant_source_children_centered_terminal_abs_le
    {n : ℕ} {as : List PositiveMass} {star U : ℕ} {B : ℝ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (hB : 0 ≤ B)
    (H : ∀Q∈actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU,
      |((actualGeneralFourCenteredForest bf hf hs hU W depth [Q]).map
        (actualGeneralFourStateResponse bf hf U W)).sum| ≤ 2*|Q.term.coefficient| *B) :
    |((actualGeneralFourCenteredForest bf hf hs hU W depth
      (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU)).map
      (actualGeneralFourStateResponse bf hf U W)).sum| ≤ 12*B := by
  let xs:=actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU
  let F:=fun (Q : NativeActualResourceState (Spin n×Bool) as 0 star)=>
    ((actualGeneralFourCenteredForest bf hf hs hU W depth [Q]).map
      (actualGeneralFourStateResponse bf hf U W)).sum
  have HD : actualGeneralFourCenteredForest bf hf hs hU W depth xs=
      xs.flatMap (fun Q=>actualGeneralFourCenteredForest bf hf hs hU W depth [Q]):=by
    unfold actualGeneralFourCenteredForest
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  change |((actualGeneralFourCenteredForest bf hf hs hU W depth xs).map
    (actualGeneralFourStateResponse bf hf U W)).sum| ≤ _
  rw [HD,List.map_flatMap,native_sum_flatMap]
  apply (native_abs_sum_map_le xs F).trans
  have Hsum : (xs.map (fun Q=>|F Q|)).sum ≤
      (xs.map (fun Q=>2*|Q.term.coefficient| *B)).sum:=List.sum_le_sum H
  have HE : (xs.map (fun Q=>2*|Q.term.coefficient| *B)).sum=
      2*((xs.map (fun Q=>|Q.term.coefficient|)).sum)*B:=by
    induction xs with
    | nil=>simp
    | cons Q qs ih=>simp only [List.map_cons,List.sum_cons,ih];ring
  apply Hsum.trans
  rw [HE]
  have HC:=actualGeneralConstantSourceChildren_coefficient_variation (n:=n) bf hf hbf hhf ho hs hU
  change (xs.map (fun Q=>|Q.term.coefficient|)).sum ≤ 6 at HC
  nlinarith [mul_le_mul_of_nonneg_right HC hB]

end OAI.SKFluctuations.Cavity
