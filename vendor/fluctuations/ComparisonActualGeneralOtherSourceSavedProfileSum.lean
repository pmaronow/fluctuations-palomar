module

public import ComparisonActualGeneralOtherSourceProfileSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

theorem actual_general_four_other_source_sum_abs_le_of_saved_profile
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as : List PositiveMass} {i star U : ℕ}
    {W seedScale base C Vcoef Vprofile : ℝ}
    (hW : 0 ≤ W) (hscale : 0 ≤ seedScale)
    (hbase : 0 ≤ base) (hC : 0 ≤ C)
    (f : ℕ→ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    (H : ∀Q∈rows,
      |(W⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q| ≤
        |Q.term.coefficient| *seedScale*
          (base*W^3+C*W*(Q.tree.forkCost f+edgeBudget 0 as f)))
    (Hcoef : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ Vcoef)
    (Hprofile : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤ Vprofile) :
    |actualGeneralFourOtherSourceErrorSum bf hf U W rows| ≤
      seedScale*(base*W^3*Vcoef+C*W*Vprofile) := by
  have Hsum : (rows.map (fun Q=>|Q.term.coefficient| *seedScale*
      (base*W^3+C*W*(Q.tree.forkCost f+edgeBudget 0 as f)))).sum =
      seedScale*(base*W^3*(rows.map (fun Q=>|Q.term.coefficient|)).sum+
        C*W*(rows.map (fun Q=>|Q.term.coefficient| *
          (Q.tree.forkCost f+edgeBudget 0 as f))).sum) := by
    clear H Hcoef Hprofile
    induction rows with
    | nil => simp
    | cons Q rows ih =>
      simp only [List.map_cons,List.sum_cons] at ih ⊢
      rw [ih]
      ring
  have Hraw := (native_abs_sum_map_le _ _).trans (List.sum_le_sum H)
  rw [Hsum] at Hraw
  apply Hraw.trans
  apply mul_le_mul_of_nonneg_left _ hscale
  have HC := mul_le_mul_of_nonneg_left Hcoef (mul_nonneg hbase (pow_nonneg hW 3))
  have HP := mul_le_mul_of_nonneg_left Hprofile (mul_nonneg hC hW)
  nlinarith only [HC,HP]

end OAI.SKFluctuations.Cavity
