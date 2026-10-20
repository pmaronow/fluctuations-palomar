module

public import SKConstants.Completion.Blueprint5.ContinuityAssembly
public import SKConstants.Completion.N19DS.Node
public import SKConstants.Completion.N19B.Node
public import SKConstants.Completion.N19M.Node
public import SKConstants.Completion.N19C.Node

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SKConstants.Completion.FW

theorem coarsePrimitiveInputBounds_holds : N19n.CoarsePrimitiveInputBoundsStatement :=
  Blueprint5.coarsePrimitiveInputBounds_of_subnodes N19DS.coarseDPathBoundsStatement_holds
    N19DS.coarseStartGapBoundsStatement_holds N19B.coarseBridgeBoundsStatement_holds
    N19M.coarseMatrixBoundsStatement_holds N19C.coarseCompletionBoundsStatement_holds

theorem coarseContinuityCommon_holds : Blueprint4.CoarseContinuityCommonStatement :=
  Blueprint5.coarseContinuityCommonStatement_of_subnodes N19DS.coarseDPathBoundsStatement_holds
    N19DS.coarseStartGapBoundsStatement_holds N19B.coarseBridgeBoundsStatement_holds
    N19M.coarseMatrixBoundsStatement_holds N19C.coarseCompletionBoundsStatement_holds

theorem coarseContinuity_holds : Blueprint.CoarseContinuityStatement :=
  Blueprint4.coarseContinuityStatement_of_common coarseContinuityCommon_holds

end SKConstants.Completion.FW
