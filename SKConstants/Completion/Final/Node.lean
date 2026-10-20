module

public import SKConstants.Completion.Final.Pinning
public import SKConstants.Completion.N0.Node
public import SKConstants.Completion.NScalar.Node
public import SKConstants.Completion.NReplay.Node
public import SKConstants.Completion.N4c.Node
public import SKConstants.Completion.N7.Node
public import SKConstants.Completion.N16.Node
public import SKConstants.Completion.N17.Node

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SKConstants.Final
open Blueprint Blueprint4

theorem perAngleLawNonnegativeExponentStatement_holds :
    Blueprint.PerAngleLawNonnegativeExponentStatement :=
  N16.PerAngleLawNonnegativeExponentStatement_holds

theorem pinningCommonStatement_holds : PinningCommonStatement := by
  intro p hf hc _hr0 hr
  exact pinningAt_of_replay_nodes replayInputLaw_holds thresholdLink_holds
    replayRowLaw_holds p hf hc.1 hc.2.1 hr

theorem pinningStatement_holds : PinningStatement :=
  pinningStatement_of_common pinningCommonStatement_holds

theorem forwardKL_of_open (hHistory : Completion.N7.ReplayDHistoryLawStatement) :
    ForwardKLStatement :=
  Completion.N7.forwardKL_holds replayInputLaw_holds thresholdLink_holds hHistory

theorem fineKL_of_open (hHistory : Completion.N7.ReplayDHistoryLawStatement)
    (hEnergy : FineEnergyStatement) : FineKLStatement :=
  fineKL_of_nodes (forwardKL_of_open hHistory) hEnergy proposalSpinMarginal_holds

end SKConstants.Final
