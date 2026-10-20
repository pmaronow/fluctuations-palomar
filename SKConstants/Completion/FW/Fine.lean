module

public import SKConstants.Completion.Blueprint5.FineAssembly
public import SKConstants.Completion.N9I.Node
public import SKConstants.Completion.N9Q2.Node
public import SKConstants.Completion.N9R.Node
public import SKConstants.Completion.N9T1.Node
public import SKConstants.Completion.N9T2b.Node
public import SKConstants.Completion.N9Z2.Node

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SKConstants.Completion.FW

theorem fineCellPastFrame_holds : N9T2b.FineCellPastFrameStatement :=
  N9T1.fineCellPastFrameStatement_holds

theorem fineCellFrozenTransport_holds : Blueprint5.FineCellFrozenTransportStatement :=
  N9T2b.fineCellFrozenTransportStatement_holds fineCellPastFrame_holds

theorem fineEnergy_of_remaining (hY : Blueprint5.FineProjectionMomentStatement)
    (hL : N9Z2.FreshEndpointLipschitzStatement) : Blueprint.FineEnergyStatement :=
  Blueprint5.fineEnergy_of_subnodes N9I.fineCellIntegrable_holds
    fineCellFrozenTransport_holds N9Q2.finePosteriorRestart_holds
    (N9Z2.fineMixedEnvelopeStatement_holds hL) N9R.fineCellRowStatisticsStatement_holds hY

end SKConstants.Completion.FW
