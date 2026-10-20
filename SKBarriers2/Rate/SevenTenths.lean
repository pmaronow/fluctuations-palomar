module
public import SKBarriers2.Interfaces
public import SKBarriers2.Bridge.Model
public import SKBarriers2.Bridge.ScalarValue
public import HexagonPaper.Main

@[expose] public section

noncomputable section
open Filter OAI.SK OAI.SK.Analytic

namespace SKBarriers2

theorem meanRate_seven_tenths (β : ℝ) (hβ : 1 < β) :
    ∃ Cb : ℝ, 0 < Cb ∧ MeanRate β (7 / 10) Cb := by
  obtain ⟨Cb, hCb, hAll⟩ := HexagonPaper.main_mean_bias β hβ
  refine ⟨Cb, hCb, ?_⟩
  change ∀ᶠ n : ℕ in atTop,
    finiteParisiInf β - quenchedPressure β n ≤
      Cb * (n : ℝ) ^ (-(7 / 10 : ℝ))
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [Bridge.finiteParisiInf_eq_parisiPDEValue,
    Bridge.quenchedPressure_eq_pressure]
  simpa only [QuantitativeFollowup.finiteBias,
    QuantitativeFollowup.parisiLimit] using (hAll n hn).2

end SKBarriers2
