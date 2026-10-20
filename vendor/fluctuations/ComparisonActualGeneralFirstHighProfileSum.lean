module

public import ComparisonActualGeneralFourFirstHighIteration
public import ComparisonActualGeneralFourFirstHighSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_general_first_high_error_sum_abs_le_of_profile
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as : List PositiveMass} {i star U : ℕ} (W C : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) (f : ℕ→ℝ)
    (Hrow : ∀Q∈rows,|actualGeneralFourFirstHighError bf hf U W Q| ≤
      C*(|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))) :
    |actualGeneralFourFirstHighErrorSum bf hf U W rows| ≤
      C*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum := by
  unfold actualGeneralFourFirstHighErrorSum
  apply (native_abs_sum_map_le _ _).trans
  apply (List.sum_le_sum Hrow).trans_eq
  rw [←List.sum_map_mul_left]

end OAI.SKFluctuations.Cavity
