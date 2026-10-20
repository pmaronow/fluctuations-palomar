module

public import SKConstants.Completion.Blueprint4.AssemblyAt

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SKConstants.Blueprint4
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal SKConstants.Blueprint

theorem witnessDecay_of_admissible4 {c sseq : ℝ} {p : Parameters}
    (hadm : Admissible4 c sseq p) (hFine : FineKLStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : SharpCoarseDominationStatement)
    (hCont : CoarseContinuityCommonStatement) (hPin : PinningCommonStatement)
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun n : ℕ => (skDisorderLaw n).real (lowFlowWitnessEvent β ((n : ℝ) ^ (-p.d))
      (Real.exp (-((n : ℝ) ^ (1 - p.q)))) 12)) atTop (𝓝 0) := by
  obtain ⟨hfe, hce4, hbe, hse, hcov, -, -⟩ := hadm
  have hcc := common_of_coarseExponents4 hce4
  have hr0 : 0 < p.r := by
    obtain ⟨hq0, hqu, hur, -, -, -⟩ := hbe
    linarith
  have hrb : p.r < p.b / 2 := hse.2.2.2.2.2.1
  have hSeq : SequenceGoodAt p sseq :=
    sequenceGoodAt_of_nodes p sseq hfe hcc hbe hse hAngle
      (fun s₂ hq hkb hzP hD => coarseHitAt_of_dominationAt p s₂ hfe hcc hbe hq hkb hzP hD
        (hDom p hfe hce4))
      (hCont p sseq hfe hcc hbe hse) (hPin p hfe hcc hr0 hrb)
  exact witnessDecayAt_of_top_nodes p sseq hFine hEnd hSeq hfe hse hcov W β hβ

theorem typicalStart_of_admissible4 {c sseq : ℝ} {p : Parameters}
    (hadm : Admissible4 c sseq p) (hBM : BrownianSystemExistsStatement)
    (hFine : FineKLStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : SharpCoarseDominationStatement)
    (hCont : CoarseContinuityCommonStatement) (hPin : PinningCommonStatement)
    (β : ℝ) (hβ : 1 < β) :
    Tendsto (fun n : ℕ => (skJointLaw n β).real
      {z | 1 / 4 < continuousHeatBathPointTV β z.1
        (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (𝓝 0) := by
  obtain ⟨Ω, _, ⟨W⟩⟩ := hBM
  have hw := witnessDecay_of_admissible4 hadm hFine hEnd hAngle hDom hCont hPin W β hβ
  obtain ⟨-, -, hbe, -, hcov, -, hcq⟩ := hadm
  obtain ⟨-, -, -, -, -, hqh⟩ := hbe
  obtain ⟨hd, -⟩ := hcov
  exact sk_joint_bad_start_decay_of_witness_twelve β c p.q p.d (1 / 4) hcq (by linarith) hd
    (by norm_num) hw

theorem witness_decay_quarter_of_top_nodes (hBM : BrownianSystemExistsStatement)
    (hFine : FineKLStatement) (hEnd : EndpointLawStatement) (hAngle : PerAngleLawNonnegativeExponentStatement)
    (hDom : SharpCoarseDominationStatement) (hCont : CoarseContinuityCommonStatement)
    (hPin : PinningCommonStatement) :
    ∀ β c : ℝ, 1 < β → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ => (skDisorderLaw n).real
        (lowFlowWitnessEvent β ((n : ℝ) ^ (-(optimizedParameters c).d))
          (Real.exp (-((n : ℝ) ^ (1 - (optimizedParameters c).q)))) 12)) atTop (𝓝 0) := by
  intro β c hβ hc hc4
  obtain ⟨Ω, _, ⟨W⟩⟩ := hBM
  exact witnessDecay_of_admissible4 (optimized_admissible4 hc hc4) hFine hEnd hAngle hDom
    hCont hPin W β hβ

theorem optimizedSKTypicalStartStatement_of_top_nodes (hBM : BrownianSystemExistsStatement)
    (hFine : FineKLStatement) (hEnd : EndpointLawStatement) (hAngle : PerAngleLawNonnegativeExponentStatement)
    (hDom : SharpCoarseDominationStatement) (hCont : CoarseContinuityCommonStatement)
    (hPin : PinningCommonStatement) : OptimizedSKTypicalStartStatement := by
  intro β c hβ hc hc4
  exact typicalStart_of_admissible4 (optimized_admissible4 hc hc4) hBM hFine hEnd hAngle hDom
    hCont hPin β hβ

theorem witness_decay_quarter_of_nodes (hBM : BrownianSystemExistsStatement)
    (hKL : ForwardKLStatement) (hEn : FineEnergyStatement)
    (hMarg : ProposalSpinMarginalStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : SharpCoarseDominationStatement)
    (hCont : CoarseContinuityCommonStatement) (hPin : PinningCommonStatement) :
    ∀ β c : ℝ, 1 < β → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ => (skDisorderLaw n).real
        (lowFlowWitnessEvent β ((n : ℝ) ^ (-(optimizedParameters c).d))
          (Real.exp (-((n : ℝ) ^ (1 - (optimizedParameters c).q)))) 12)) atTop (𝓝 0) :=
  witness_decay_quarter_of_top_nodes hBM (fineKL_of_nodes hKL hEn hMarg) hEnd hAngle hDom
    hCont hPin

theorem optimizedSKTypicalStartStatement_of_nodes (hBM : BrownianSystemExistsStatement)
    (hKL : ForwardKLStatement) (hEn : FineEnergyStatement)
    (hMarg : ProposalSpinMarginalStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : SharpCoarseDominationStatement)
    (hCont : CoarseContinuityCommonStatement) (hPin : PinningCommonStatement) :
    OptimizedSKTypicalStartStatement :=
  optimizedSKTypicalStartStatement_of_top_nodes hBM (fineKL_of_nodes hKL hEn hMarg) hEnd
    hAngle hDom hCont hPin

theorem typical_start_quarter_g4_of_nodes (hBM : BrownianSystemExistsStatement)
    (hKL : ForwardKLStatement) (hEn : FineEnergyStatement)
    (hMarg : ProposalSpinMarginalStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : SharpCoarseDominationStatement)
    (hCont : CoarseContinuityCommonStatement) (hPin : PinningCommonStatement) :
    ∀ β c : ℝ, 1 < β → 0 < c → c < 1 / 4 →
      Tendsto (fun n : ℕ => (skDisorderLaw n).real
        (lowFlowWitnessEvent β ((n : ℝ) ^ (-(g4Parameters c).d))
          (Real.exp (-((n : ℝ) ^ (1 - (g4Parameters c).q)))) 12)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (skJointLaw n β).real
        {z | 1 / 4 < continuousHeatBathPointTV β z.1
          (Real.exp ((n : ℝ) ^ (1 - c))) z.2}) atTop (𝓝 0) := by
  intro β c hβ hc hc4
  have hFine := fineKL_of_nodes hKL hEn hMarg
  refine ⟨?_, typicalStart_of_admissible4 (g4_admissible4 hc hc4) hBM hFine hEnd hAngle hDom
    hCont hPin β hβ⟩
  obtain ⟨Ω, _, ⟨W⟩⟩ := hBM
  exact witnessDecay_of_admissible4 (g4_admissible4 hc hc4) hFine hEnd hAngle hDom hCont hPin
    W β hβ

theorem typical_start_one_twentieth_of_sharp_nodes (hBM : BrownianSystemExistsStatement)
    (hKL : ForwardKLStatement) (hEn : FineEnergyStatement)
    (hMarg : ProposalSpinMarginalStatement) (hEnd : EndpointLawStatement)
    (hAngle : PerAngleLawNonnegativeExponentStatement) (hDom : SharpCoarseDominationStatement)
    (hCont : CoarseContinuityCommonStatement) (hPin : PinningCommonStatement) :
    ∀ β : ℝ, 1 < β → Tendsto (fun n : ℕ => (skJointLaw n β).real
      {z | 1 / 4 < continuousHeatBathPointTV β z.1
        (Real.exp ((n : ℝ) ^ (1 - (1 / 20 : ℝ)))) z.2}) atTop (𝓝 0) :=
  typicalStart_of_admissible4 g0_admissible4 hBM (fineKL_of_nodes hKL hEn hMarg) hEnd hAngle
    hDom hCont hPin

end SKConstants.Blueprint4
