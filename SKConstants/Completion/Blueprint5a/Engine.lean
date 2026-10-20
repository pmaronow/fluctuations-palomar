module

public import SKConstants.Completion.Blueprint5a.AssemblySJ3
public import SKConstants.Completion.Blueprint5a.AssemblySJ7
public import SKConstants.Completion.Blueprint4.SharpEngine

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SKConstants.Blueprint5a
open SKConstants.Blueprint4

theorem sharpRowConcentration_of_subnodes (h31 : QueryRowIntegralExistsStatement)
    (h32a : PreSupportQueryDriverStatement) (h32b : SupportFieldItoStatement)
    (h32m : SupportFieldTargetMeasurableStatement)
    (h33a : PostSupportInformationItoStatement) (h33b : PostSupportPotentialStatement)
    (h33p : PostSupportProfileStatement)
    (h71 : RefinedResidualLimitStatement) (h73 : QuadraticGroupLimitStatement)
    (h74a : SignSymmetrizationStatement) (h74b : LinearGroupSubgaussianStatement)
    (h75 : PredictableGroupMGFStatement) (h76 : LagGroupMGFStatement) :
    SharpRowConcentrationStatement :=
  sharpRowConcentration_of_engine
    (jointEndpointIdentity_of_subnodes h31 h32a h32b h32m h33a h33b h33p)
    (growingResidualMGF_of_subnodes h71 h73 h74a h74b h75 h76)

end SKConstants.Blueprint5a
