module
public import SKConstants.Completion.LM3.ScalarCancellation
public import SKConstants.Completion.LM3.TerminalLinkBridge
public import SKConstants.Completion.LM3.ForwardKL
public import SKConstants.Completion.LM3.RowScalarReduction
public import SKConstants.Completion.LM3.SourceReplayBridge

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualReplay_forward_KL_finite
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    klDiv ((growingReplayLinkedLaw W β hβ δ ranks q V).map (replayOutput δ ranks q))
      (skJointLaw (ranks + q) β) < ∞ :=
  lt_of_le_of_lt (actualReplay_forward_KL W β hβ δ hδ ranks q V I hI) ENNReal.ofReal_lt_top

theorem actualReplay_Gibbs_KL_exists
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    ∃ I : GrowingReplaySpace Ω δ ranks q → ℝ,
      IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I ∧
      IsProbabilityMeasure (growingReplayGibbsReference W β hβ δ hδ ranks q V I) ∧
      klDiv (growingReplayLinkedLaw W β hβ δ ranks q V)
        (growingReplayGibbsReference W β hβ δ hδ ranks q V I) =
        ENNReal.ofReal (∫ u, growingReplayGibbsLogRatio W β hβ δ hδ ranks q V I u
          ∂growingReplayLinkedLaw W β hβ δ ranks q V) ∧
      klDiv ((growingReplayLinkedLaw W β hβ δ ranks q V).map (replayOutput δ ranks q))
        (skJointLaw (ranks + q) β) < ∞ := by
  obtain ⟨I, hI, _⟩ := actualReplayGaussianReference_integral_exists W β hβ δ hδ ranks q V
  exact ⟨I, hI, growingReplayGibbsReference_probability W β hβ δ hδ ranks q V I hI,
    growingReplayGibbs_klDiv_eq W β hβ δ hδ ranks q V I hI,
    actualReplay_forward_KL_finite W β hβ δ hδ ranks q V I hI⟩

theorem actualSource_forward_KL_finite
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (hn : 0 < ranks + q) :
    klDiv ((M1.SourceLinkedLaw W β hβ δ ranks q).map (sourceOutput W β hβ δ ranks q))
      (skJointLaw (ranks + q) β) < ∞ := by
  obtain ⟨I, hI, _⟩ := actualReplayGaussianReference_integral_exists W β hβ δ hδ ranks q
    (scalarGrowingSourceHorizon δ q)
  rw [sourceLinkedLaw_output_eq_replay W β hβ δ ranks q hn]
  exact actualReplay_forward_KL_finite W β hβ δ hδ ranks q _ I hI

end SKConstants.Completion.LM3
