module

public import SKConstants.Completion.NDH.DHistory
public import SKConstants.Completion.NDH.MixedRows
public import SKConstants.Completion.N7.Node
public import SKConstants.Completion.NReplay.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SKConstants.Completion.NDH
open SKConstantsOAI.ZeroTemperatureSK

theorem replayDHistoryLaw_holds : N7.ReplayDHistoryLawStatement := by
  intro Ω _ W β hβ δ hδ r q hr
  exact canonicalObservationDHistory_at_horizon W β hβ δ hδ r q
    (lt_of_lt_of_le hr (Nat.le_add_right r q))

theorem sourceMixedRowsLaw_holds {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) :
    LGram.SourceMixedRowsLawStatement W β hβ δ r K :=
  ⟨(LGram.measurable_literalSourceRows W β hβ δ r K).aemeasurable,
    sourceMixedRows_law W β hβ δ hδ r K⟩

theorem forwardKL_holds : Blueprint.ForwardKLStatement :=
  N7.forwardKL_holds Blueprint.replayInputLaw_holds Blueprint.thresholdLink_holds
    replayDHistoryLaw_holds

end SKConstants.Completion.NDH
