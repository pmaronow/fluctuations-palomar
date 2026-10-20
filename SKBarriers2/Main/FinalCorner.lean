module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import SKBarriers2.Main.Final
public import SKBarriers2.Rate.AllLean

@[expose] public section

/-! The frozen main and subcritical statements, conditional only on the
section 3 corner inputs. The rate inputs come from all-lean QuantitativePaper
through `Rate/AllLean.lean`. -/

namespace SKBarriers2

theorem mainStatement_of_cornerInputs'
    (hcorner : ∀ β (hβ : 1 < β), CornerInputs β (scalarData β hβ)) :
    OAI.SK.Strengthened.MainStatement :=
  mainStatement_of_cornerInputs meanRate_two_thirds varianceCap_seven_fifteenths hcorner

theorem subcriticalStatement_of_cornerInputs'
    (hcorner : ∀ β (hβ : 1 < β), CornerInputs β (scalarData β hβ)) :
    OAI.SK.Strengthened.SubcriticalStatement :=
  subcriticalStatement_of_cornerInputs meanRate_two_thirds varianceCap_seven_fifteenths hcorner

end SKBarriers2
