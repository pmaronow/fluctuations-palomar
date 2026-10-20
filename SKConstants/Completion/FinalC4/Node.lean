module

public import SKConstants.Completion.Final.Assembly
public import SKConstants.Completion.NDH.Node
public import SKConstants.Completion.FW.Sharp
public import SKConstants.Completion.FW.Fine
public import SKConstants.Completion.FW.Continuity

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace SKConstants.FinalC4
open Completion

theorem fineKL_of_remaining (hY : Blueprint5.FineProjectionMomentStatement)
    (hL : N9Z2.FreshEndpointLipschitzStatement) : Blueprint.FineKLStatement :=
  Final.fineKL_of_open NDH.replayDHistoryLaw_holds (FW.fineEnergy_of_remaining hY hL)

theorem witness_decay_quarter_of_remaining (hY : Blueprint5.FineProjectionMomentStatement)
    (hL : N9Z2.FreshEndpointLipschitzStatement) :
    ∀ beta c : ℝ, 1 < beta → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ => (skDisorderLaw n).real
        (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(optimizedParameters c).d))
          (Real.exp (-((n : ℝ) ^ (1 - (optimizedParameters c).q)))) 12)) atTop (𝓝 0) :=
  Final.witness_decay_quarter_of_open NDH.replayDHistoryLaw_holds
    (FW.fineEnergy_of_remaining hY hL) FW.sharpCoarseDomination_holds FW.coarseContinuityCommon_holds

theorem optimizedSKTypicalStartStatement_of_remaining
    (hY : Blueprint5.FineProjectionMomentStatement)
    (hL : N9Z2.FreshEndpointLipschitzStatement) : SKConstants.OptimizedSKTypicalStartStatement :=
  Final.optimizedSKTypicalStartStatement_of_open NDH.replayDHistoryLaw_holds
    (FW.fineEnergy_of_remaining hY hL) FW.sharpCoarseDomination_holds FW.coarseContinuityCommon_holds

theorem witness_decay_one_twentieth_of_remaining
    (hY : Blueprint5.FineProjectionMomentStatement)
    (hL : N9Z2.FreshEndpointLipschitzStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(1 / 200 : ℝ)))
        (Real.exp (-((n : ℝ) ^ (1 - (3 / 50 : ℝ))))) 12)) atTop (𝓝 0) := by
  intro beta hbeta
  obtain ⟨Ω, _, ⟨W⟩⟩ := Blueprint.brownianSystemExists_holds
  exact Blueprint4.witnessDecay_of_admissible4 Blueprint4.g0_admissible4
    (fineKL_of_remaining hY hL) N17.endpointLaw_holds
    Final.perAngleLawNonnegativeExponentStatement_holds FW.sharpCoarseDomination_holds
    FW.coarseContinuityCommon_holds Final.pinningCommonStatement_holds W beta hbeta

theorem typical_start_one_twentieth_of_remaining
    (hY : Blueprint5.FineProjectionMomentStatement)
    (hL : N9Z2.FreshEndpointLipschitzStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | 1 / 4 < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - (1 / 20 : ℝ)))) z.2}) atTop (𝓝 0) := by
  intro beta hbeta
  exact optimizedSKTypicalStartStatement_of_remaining hY hL beta (1 / 20) hbeta
    (by norm_num) (by norm_num)

end SKConstants.FinalC4
