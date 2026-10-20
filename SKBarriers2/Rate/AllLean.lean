module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import SKBarriers2.Interfaces
public import SKBarriers2.Bridge.Model
public import SKBarriers2.Bridge.ScalarValue
public import QuantitativePaper.MainFixedTemperatureFluctuations

@[expose] public section

/-! The fixed-temperature all-lean bounds in the frozen upstream interfaces.

The physical models agree exactly by `Bridge.Model`; the scalar infima agree
for every real β by `Bridge.finiteParisiInf_eq_parisiPDEValue`. Consequently
the only hypothesis in either rate input is `1 < β`, as in the source theorem.
The same positive constant can be used for both inputs.
-/

noncomputable section
open Filter OAI.SK OAI.SK.Analytic

namespace SKBarriers2

/-- Both all-lean upper bounds, with one common positive constant. -/
theorem meanRate_varianceCap_allLean (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ MeanRate β (2 / 3) C ∧ VarianceCap β (7 / 15) C := by
  obtain ⟨_c, C, N0, _hc, hC, _hN0, hbound⟩ :=
    QuantitativePaper.fixed_temperature_fluctuations β hβ
  refine ⟨C, hC, ?_, ?_⟩
  · change ∀ᶠ n : ℕ in atTop,
      finiteParisiInf β - quenchedPressure β n ≤ C * (n : ℝ) ^ (-(2 / 3 : ℝ))
    filter_upwards [eventually_ge_atTop N0] with n hn
    rw [Bridge.finiteParisiInf_eq_parisiPDEValue, Bridge.quenchedPressure_eq_pressure]
    exact (hbound n hn).2.2.2
  · change ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.variance (fun J : Disorder n => logPartition β J) (disorderLaw n) ≤
        C * (n : ℝ) ^ (7 / 15 : ℝ)
    filter_upwards [eventually_ge_atTop N0] with n hn
    rw [Bridge.variance_logPartition_eq_freeEnergyVariance]
    exact (hbound n hn).2.1

theorem meanRate_two_thirds (β : ℝ) (hβ : 1 < β) :
    ∃ Cb : ℝ, 0 < Cb ∧ MeanRate β (2 / 3) Cb := by
  obtain ⟨C, hC, hmean, _hvar⟩ := meanRate_varianceCap_allLean β hβ
  exact ⟨C, hC, hmean⟩

theorem varianceCap_seven_fifteenths (β : ℝ) (hβ : 1 < β) :
    ∃ Cv : ℝ, 0 < Cv ∧ VarianceCap β (7 / 15) Cv := by
  obtain ⟨C, hC, _hmean, hvar⟩ := meanRate_varianceCap_allLean β hβ
  exact ⟨C, hC, hvar⟩

end SKBarriers2
