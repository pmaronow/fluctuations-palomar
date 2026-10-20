module

public import SKProof.OriginalQStrongExclusion

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace OAI.SKFluctuations.LaplaceWindowFormalization

theorem main_fluctuation_statement_unconditional_original_q :
    OAI.SKFluctuations.MainFluctuationStatement :=
  main_fluctuation_statement_of_strong_exclusion strong_exclusion_inputs_original_q

end OAI.SKFluctuations.LaplaceWindowFormalization
