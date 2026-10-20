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

/-- Convergence is a proved conclusion alongside the lower mean-bias bound. -/
theorem corollary_1_7 :
    (∀ β : ℝ, 1 < β →
      Tendsto (OAI.SKFluctuations.MeanBias.countingPressure β) atTop
        (𝓝 (OAI.SKFluctuations.MeanBias.limitingPressure β))) ∧
    OAI.SKFluctuations.MeanBias.LowerBoundStatement := by
  refine ⟨?_,
    OAI.SKFluctuations.LaplaceWindowFormalization.mean_bias_lower_bound_unconditional⟩
  intro β hβ
  have hβp : 0 < β := zero_lt_one.trans hβ
  have hP : OAI.SKFluctuations.MeanBias.countingPressure β =
      Paper.finiteSKFreeEnergy β 0 := by
    funext n
    rw [OAI.SKFluctuations.MeanBias.countingPressure_eq_pressure]
    exact QuantitativePaper.pressure_eq_finiteSKFreeEnergy n β
  rw [OAI.SKFluctuations.MeanBias.limitingPressure_eq_parisiPDEValue β hβp, hP]
  exact Paper.physicalParisiFormula β 0 hβp

end LowerUpperBounds
