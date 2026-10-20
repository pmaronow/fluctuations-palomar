module

public import SKConstants.Completion.Blueprint.AssemblyWitness
public import SKConstants.Completion.Blueprint.AssemblySequence
public import SKConstants.Completion.Blueprint.AssemblyCoarse
public import SKConstants.Completion.Blueprint.AssemblyFine

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SKConstants.Blueprint
open SKConstantsOAI.ZeroTemperatureSK

theorem g0Parameters_d : g0Parameters.d = 1 / 200 := rfl
theorem g0Parameters_q : g0Parameters.q = 3 / 50 := rfl

theorem witness_decay_one_twentieth_of_top_nodes
    (hBM : BrownianSystemExistsStatement) (hFine : FineKLStatement)
    (hEnd : EndpointLawStatement) (hSeq : SequenceGoodStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(1 / 200 : ℝ)))
        (Real.exp (-((n : ℝ) ^ (1 - (3 / 50 : ℝ))))) 12)) atTop (𝓝 0) := by
  intro beta hbeta
  obtain ⟨Ω, _, ⟨W⟩⟩ := hBM
  obtain ⟨hfe, hce, hbe, hse, hcov, _, _⟩ := g0_admissible
  have h := witness_decay_of_top_nodes g0Parameters g0Sequence hFine hEnd hSeq hfe hce hbe hse
    hcov W beta hbeta
  simpa only [g0Parameters_d, g0Parameters_q] using h

theorem typical_start_one_twentieth_of_top_nodes
    (hBM : BrownianSystemExistsStatement) (hFine : FineKLStatement)
    (hEnd : EndpointLawStatement) (hSeq : SequenceGoodStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | 1 / 4 < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - (1 / 20 : ℝ)))) z.2}) atTop (𝓝 0) := by
  intro beta hbeta
  exact sk_joint_bad_start_decay_of_witness_twelve beta (1 / 20) (3 / 50) (1 / 200) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (witness_decay_one_twentieth_of_top_nodes hBM hFine hEnd hSeq beta hbeta)

theorem witness_decay_one_twentieth_of_middle_nodes
    (hBM : BrownianSystemExistsStatement) (hFine : FineKLStatement)
    (hEnd : EndpointLawStatement) (hAngle : PerAngleLawNonnegativeExponentStatement)
    (hHit : CoarseHitStatement) (hCont : CoarseContinuityStatement)
    (hPin : PinningStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(1 / 200 : ℝ)))
        (Real.exp (-((n : ℝ) ^ (1 - (3 / 50 : ℝ))))) 12)) atTop (𝓝 0) :=
  witness_decay_one_twentieth_of_top_nodes hBM hFine hEnd
    (sequenceGood_of_nodes hAngle hHit hCont hPin)

theorem typical_start_one_twentieth_of_middle_nodes
    (hBM : BrownianSystemExistsStatement) (hFine : FineKLStatement)
    (hEnd : EndpointLawStatement) (hAngle : PerAngleLawNonnegativeExponentStatement)
    (hHit : CoarseHitStatement) (hCont : CoarseContinuityStatement)
    (hPin : PinningStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | 1 / 4 < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - (1 / 20 : ℝ)))) z.2}) atTop (𝓝 0) :=
  typical_start_one_twentieth_of_top_nodes hBM hFine hEnd
    (sequenceGood_of_nodes hAngle hHit hCont hPin)

theorem witness_decay_one_twentieth_of_nodes
    (hBM : BrownianSystemExistsStatement) (hKL : ForwardKLStatement)
    (hEn : FineEnergyStatement) (hMarg : ProposalSpinMarginalStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : CoarseDominationStatement)
    (hCont : CoarseContinuityStatement) (hPin : PinningStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skDisorderLaw n).real
      (lowFlowWitnessEvent beta ((n : ℝ) ^ (-(1 / 200 : ℝ)))
        (Real.exp (-((n : ℝ) ^ (1 - (3 / 50 : ℝ))))) 12)) atTop (𝓝 0) :=
  witness_decay_one_twentieth_of_middle_nodes hBM (fineKL_of_nodes hKL hEn hMarg) hEnd
    hAngle (coarseHit_of_domination hDom) hCont hPin

theorem typical_start_one_twentieth_of_nodes
    (hBM : BrownianSystemExistsStatement) (hKL : ForwardKLStatement)
    (hEn : FineEnergyStatement) (hMarg : ProposalSpinMarginalStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : CoarseDominationStatement)
    (hCont : CoarseContinuityStatement) (hPin : PinningStatement) :
    ∀ beta : ℝ, 1 < beta → Tendsto (fun n : ℕ => (skJointLaw n beta).real
      {z | 1 / 4 < continuousHeatBathPointTV beta z.1
        (Real.exp ((n : ℝ) ^ (1 - (1 / 20 : ℝ)))) z.2}) atTop (𝓝 0) :=
  typical_start_one_twentieth_of_middle_nodes hBM (fineKL_of_nodes hKL hEn hMarg) hEnd
    hAngle (coarseHit_of_domination hDom) hCont hPin

end SKConstants.Blueprint
