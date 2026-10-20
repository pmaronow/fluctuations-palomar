module

public import SKProof.MeanBiasBridge
public import SKProof.OriginalQUnconditionalMain

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace OAI.SKFluctuations.LaplaceWindowFormalization

theorem mean_bias_lower_bound_unconditional : MeanBias.LowerBoundStatement :=
  MeanBias.lowerBound_of_main_statement main_fluctuation_statement_unconditional_original_q

end OAI.SKFluctuations.LaplaceWindowFormalization
