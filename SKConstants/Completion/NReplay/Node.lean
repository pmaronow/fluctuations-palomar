module

public import SKConstants.Completion.NReplay.ProposalLaw

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SKConstants.Blueprint

open SKConstantsOAI.ZeroTemperatureSK

theorem replayInputLaw_holds : ReplayInputLawStatement :=
  NReplay.replayInput_law

theorem thresholdLink_holds : ThresholdLinkStatement := by
  intro Ω _ W β hβ δ r₀ q
  exact NReplay.threshold_terminalLinkedLaw β (M1.Horizon δ q) (M1.ReplayLaw W δ r₀ q)
    (actualParisiGrowingReplayField W β hβ δ r₀ q (M1.Horizon δ q))
    (M1.measurable_ReplayField W β hβ δ r₀ q _)

theorem proposalSpinMarginal_holds : ProposalSpinMarginalStatement := by
  intro Ω _ W β hβ δ hδ r₀ q hr₀ n h
  exact NReplay.replayProposalGen_spin_marginal W β hβ δ hδ r₀ q (by omega) h

end SKConstants.Blueprint
