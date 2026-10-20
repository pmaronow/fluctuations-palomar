module

public import SKConstants.Completion.Final.Node
public import SKConstants.Completion.Blueprint.Assembly
public import SKConstants.Completion.Blueprint4.Assembly4

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

namespace SKConstants.Final
open Blueprint Blueprint4

theorem witness_decay_one_twentieth_of_open
    (hHistory : Completion.N7.ReplayDHistoryLawStatement) (hEnergy : FineEnergyStatement)
    (hDom : CoarseDominationStatement) (hCont : CoarseContinuityStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(1 / 200 : ℝ)))
        (Real.exp (-((n : ℝ) ^ (1 - (3 / 50 : ℝ))))) 12)) atTop (𝓝 0) :=
  witness_decay_one_twentieth_of_middle_nodes brownianSystemExists_holds
    (fineKL_of_open hHistory hEnergy) Completion.N17.endpointLaw_holds
    perAngleLawNonnegativeExponentStatement_holds (coarseHit_of_domination hDom)
    hCont pinningStatement_holds

theorem typical_start_one_twentieth_of_open
    (hHistory : Completion.N7.ReplayDHistoryLawStatement) (hEnergy : FineEnergyStatement)
    (hDom : CoarseDominationStatement) (hCont : CoarseContinuityStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | 1 / 4 < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - (1 / 20 : ℝ)))) z.2}) atTop (𝓝 0) :=
  typical_start_one_twentieth_of_middle_nodes brownianSystemExists_holds
    (fineKL_of_open hHistory hEnergy) Completion.N17.endpointLaw_holds
    perAngleLawNonnegativeExponentStatement_holds (coarseHit_of_domination hDom)
    hCont pinningStatement_holds

theorem typical_start_one_twentieth_of_open_common
    (hHistory : Completion.N7.ReplayDHistoryLawStatement) (hEnergy : FineEnergyStatement)
    (hDom : CoarseDominationStatement) (hCont : CoarseContinuityCommonStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | 1 / 4 < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - (1 / 20 : ℝ)))) z.2}) atTop (𝓝 0) :=
  typical_start_one_twentieth_of_open hHistory hEnergy hDom
    (coarseContinuityStatement_of_common hCont)

theorem witness_decay_quarter_of_open
    (hHistory : Completion.N7.ReplayDHistoryLawStatement) (hEnergy : FineEnergyStatement)
    (hDom : SharpCoarseDominationStatement) (hCont : CoarseContinuityCommonStatement) :
    ∀ beta c : ℝ, 1 < beta → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ => (skDisorderLaw n).real
        (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(optimizedParameters c).d))
          (Real.exp (-((n : ℝ) ^ (1 - (optimizedParameters c).q)))) 12)) atTop (𝓝 0) :=
  witness_decay_quarter_of_top_nodes brownianSystemExists_holds
    (fineKL_of_open hHistory hEnergy) Completion.N17.endpointLaw_holds
    perAngleLawNonnegativeExponentStatement_holds hDom hCont pinningCommonStatement_holds

theorem optimizedSKTypicalStartStatement_of_open
    (hHistory : Completion.N7.ReplayDHistoryLawStatement) (hEnergy : FineEnergyStatement)
    (hDom : SharpCoarseDominationStatement) (hCont : CoarseContinuityCommonStatement) :
    OptimizedSKTypicalStartStatement :=
  optimizedSKTypicalStartStatement_of_top_nodes brownianSystemExists_holds
    (fineKL_of_open hHistory hEnergy) Completion.N17.endpointLaw_holds
    perAngleLawNonnegativeExponentStatement_holds hDom hCont pinningCommonStatement_holds

end SKConstants.Final
