module

public import SKConstants.Completion.Blueprint5a.AssemblySJ3
public import SKConstants.Completion.Blueprint5a.AssemblySJ7
public import SKConstants.Completion.S31.Node
public import SKConstants.Completion.S32a.Node
public import SKConstants.Completion.X32B.Node
public import SKConstants.Completion.X33C.Node
public import SKConstants.Completion.S33b.Node
public import SKConstants.Completion.BP5aF.Node
public import SKConstants.Completion.X73A.Node
public import SKConstants.Completion.N13A.Node
public import SKConstants.Completion.N13bc.Final.Node
public import SKConstants.Completion.NW.Node
public import SKConstants.Completion.NT2.Node
public import SKConstants.Completion.NT3.Node
public import SKConstants.Completion.NL1.Node

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SKConstants.Completion.FW

theorem jointEndpointIdentity_holds : Blueprint4.JointEndpointIdentityStatement :=
  Blueprint5a.jointEndpointIdentity_of_subnodes S31.queryRowIntegralExists_holds
    S32a.preSupportQueryDriver_holds X32B.supportFieldIto_holds
    BP5aF.supportFieldTargetMeasurable_holds X33C.postSupportInformationIto_holds
    S33b.postSupportPotential_holds BP5aF.postSupportProfile_holds

theorem growingResidualMGF_holds : Blueprint4.GrowingResidualMGFStatement :=
  Blueprint5a.growingResidualMGF_of_subnodes S71.refinedResidualLimit_holds
    X73A.quadraticGroupLimit_holds Blueprint5a.signSymmetrization_holds
    (S745.linearGroupSubgaussian_holds S72.coarseCoefficientBudget_holds)
    (S745.predictableGroupMGF_holds S72.coarseCoefficientBudget_holds)
    S76.lagGroupMGF_holds

theorem sharpRowTransport_holds : NT3.SharpRowTransportStatement :=
  NT2.sharpTransportT2_holds

theorem sharpTransport_holds : N13A.SharpTransportStatement :=
  NT3.sharpTransport_holds sharpRowTransport_holds

theorem sharpCoarseDomination_holds : Blueprint4.SharpCoarseDominationStatement :=
  N13A.sharpCoarseDomination_holds jointEndpointIdentity_holds growingResidualMGF_holds
    NW.sharpWeightedStatement_holds N13bc.sharpGramStatement_holds
    NL1.sharpLinearEnergy_holds sharpTransport_holds

end SKConstants.Completion.FW
