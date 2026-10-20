module

public import SKConstants.Completion.FinalC4.Node
public import SKConstants.Completion.L1.Node
public import SKConstants.Completion.Y1.Node

@[expose] public section
set_option autoImplicit false

namespace SKConstants.Completion.Main

theorem optimizedSKTypicalStartStatement_holds : SKConstants.OptimizedSKTypicalStartStatement :=
  SKConstants.FinalC4.optimizedSKTypicalStartStatement_of_remaining
    SKConstants.Completion.Y1.fineProjectionMomentStatement_holds
    SKConstants.Completion.L1.freshEndpointLipschitzStatement_holds

end SKConstants.Completion.Main
