module

public import SKBarriers2.Main.RateParametric
public import SKBarriers2.Rate.SevenTenths

@[expose] public section
noncomputable section

namespace SKBarriers2

theorem conditionalRateData_seven_tenths {β : ℝ} (hβ : 1 < β) :
    Nonempty (ConditionalRateData β (7 / 10)) := by
  exact conditionalRateData_of_cornerInputs_parametric hβ (scalarData β hβ)
    (by norm_num) (by norm_num) (meanRate_seven_tenths β hβ)
    (varianceCap_seven_fifteenths β hβ) (by norm_num)
    (scalarData_cornerInputs_closed β hβ)

theorem mainStatementSevenThirty : OAI.SK.Strengthened.MainStatementAt (7 / 30) := by
  have h := mainStatementAt_of_rate_data (γ := (7 / 10 : ℝ))
    (fun _ hβ => conditionalRateData_seven_tenths hβ)
  simpa only [show ((7 : ℝ) / 10) / 3 = (7 : ℝ) / 30 by norm_num] using h

theorem subcriticalStatementSevenThirty :
    OAI.SK.Strengthened.SubcriticalStatementBelow (7 / 30) := by
  have h := subcriticalStatementBelow_of_rate_data (γ := (7 / 10 : ℝ))
    (fun _ hβ => conditionalRateData_seven_tenths hβ)
  simpa only [show ((7 : ℝ) / 10) / 3 = (7 : ℝ) / 30 by norm_num] using h

end SKBarriers2
