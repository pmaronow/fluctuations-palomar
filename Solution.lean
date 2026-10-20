module

public import SKBarriers2.Main.SevenThirty
public import SKConstants.Completion.Main.Theorem
public import SKProof.OriginalQUnconditionalMain
public import SKProof.MeanBiasLowerBound

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace LowerUpperBounds

theorem theorem_1_1 : OAI.SK.Strengthened.MainStatementAt (7 / 30) :=
  SKBarriers2.mainStatementSevenThirty

theorem corollary_1_2 : OAI.SK.Strengthened.SubcriticalStatementBelow (7 / 30) :=
  SKBarriers2.subcriticalStatementSevenThirty

theorem theorem_1_3 :
    ∀ (beta c : ℝ), 1 < beta → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ ↦ (SKConstants.skJointLaw n beta).real
        {z | (1 / 4 : ℝ) < SKConstants.continuousHeatBathPointTV beta z.1
          (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (𝓝 0) :=
  SKConstants.Completion.Main.optimizedSKTypicalStartStatement_holds

theorem theorem_1_6 : OAI.SKFluctuations.MainFluctuationStatement :=
  OAI.SKFluctuations.LaplaceWindowFormalization.main_fluctuation_statement_unconditional_original_q

theorem corollary_1_7 : OAI.SKFluctuations.MeanBias.LowerBoundStatement :=
  OAI.SKFluctuations.LaplaceWindowFormalization.mean_bias_lower_bound_unconditional

end LowerUpperBounds
