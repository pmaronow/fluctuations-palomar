module

public import SKConstants.Completion.LQ.ActualGrowingQuadrature

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal BigOperators Interval
namespace SKConstants.Completion.LQ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actual_energy_overshoot (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T V : ℝ≥0) (hTV : T ≤ V) :
    0 ≤ actualParisiEnergyReference W β V - actualParisiEnergyReference W β T ∧
      actualParisiEnergyReference W β V - actualParisiEnergyReference W β T ≤
        actualParisiFullSusceptibilitySquareExpected W β T * ((V : ℝ) - (T : ℝ)) := by
  have H := energy_overshoot (actualParisiFullSusceptibilitySquareExpected W β)
    (fun v => actualParisiFullSusceptibilityExpected W β v * actualParisiQueryRho W β v)
    T.coe_nonneg (show (T : ℝ) ≤ V by exact_mod_cast hTV)
    (fun t _ht => (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1)
    (actual_square_profile_antitone W β hβ)
    (fun t _ht => actual_query_integrand_bounds W β hβ t)
    (((continuous_actualParisiFullSusceptibilitySquareExpected W β).sqrt.mul
      ((continuous_actualParisiFullSusceptibilityExpected W β).mul
        (continuous_actualParisiQueryRho W β))).intervalIntegrable 0 V)
  simpa only [actual_energy_reference_eq] using H

theorem actual_information_overshoot (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T V : ℝ≥0) (hTV : T ≤ V) :
    0 ≤ actualParisiEntropyReference W β V - actualParisiEntropyReference W β T ∧
      actualParisiEntropyReference W β V - actualParisiEntropyReference W β T ≤
        (β^2 / 2) * actualParisiFullSusceptibilitySquareExpected W β T * ((V : ℝ) - (T : ℝ)) := by
  have H := information_overshoot (actualParisiFullSusceptibilitySquareExpected W β)
    (actualParisiFullEntropyRateExpected W β) (β^2) (sq_nonneg β)
    T.coe_nonneg (show (T : ℝ) ≤ V by exact_mod_cast hTV)
    (fun t _ht => (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1)
    (actual_square_profile_antitone W β hβ)
    (fun t _ht => actualParisiFullEntropyRateExpected_bounds W β t)
    (((continuous_actualParisiFullSusceptibilitySquareExpected W β).mul
      (continuous_actualParisiFullEntropyRateExpected W β)).intervalIntegrable 0 V)
  simpa only [actual_information_reference_eq W β hβ V V.coe_nonneg,
    actual_information_reference_eq W β hβ T T.coe_nonneg] using H

theorem actual_stopped_energy_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (T : ℝ≥0) (hT : 0 < T)
    (hscale : (δ : ℝ) * Real.exp ((T : ℝ) / 4) ≤ 1) :
    |actualParisiGrowingEnergySum W β δ (growingQueryStop δ hδ T - 1) - actualParisiEnergyReference W β T| ≤
      (1 / β^2 + 33 * Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ) + 1) / 2)) * (δ : ℝ) +
        actualParisiFullSusceptibilitySquareExpected W β T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
  obtain ⟨hK, _hcount, hreach, hover, hcell⟩ := mesh_stop_geometry δ hδ T hT hscale
  have HE := actual_growing_energy_error W β hβ δ hδ (growingQueryStop δ hδ T - 1) (by
    intro i hi
    rw [hK] at hi
    exact_mod_cast (hcell i hi).trans hscale)
  rw [hK] at HE
  have HO := actual_energy_overshoot W β hβ T (growingQueryTime δ (growingQueryStop δ hδ T))
    (growingQueryStop_reaches δ hδ T)
  have HO' : |actualParisiEnergyReference W β (growingQueryTime δ (growingQueryStop δ hδ T)) -
      actualParisiEnergyReference W β T| ≤
        actualParisiFullSusceptibilitySquareExpected W β T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
    rw [abs_of_nonneg HO.1]
    calc
      _ ≤ actualParisiFullSusceptibilitySquareExpected W β T *
          ((growingQueryTime δ (growingQueryStop δ hδ T) : ℝ) - T) := HO.2
      _ ≤ actualParisiFullSusceptibilitySquareExpected W β T * ((δ : ℝ) * Real.exp ((T : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (by change meshTime δ (growingQueryStop δ hδ T) - T ≤ _; linarith)
          (actualParisiFullSusceptibilitySquareExpected_bounds W β T).1
      _ = _ := by ring
  exact (abs_sub_le _ (actualParisiEnergyReference W β (growingQueryTime δ (growingQueryStop δ hδ T))) _).trans
    (add_le_add HE HO')

theorem actual_stopped_information_error (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (T : ℝ≥0) (hT : 0 < T)
    (hscale : (δ : ℝ) * Real.exp ((T : ℝ) / 4) ≤ 1) :
    0 ≤ actualParisiGrowingEntropyFrozen W β δ (growingQueryStop δ hδ T - 1) - actualParisiEntropyReference W β T ∧
      actualParisiGrowingEntropyFrozen W β δ (growingQueryStop δ hδ T - 1) - actualParisiEntropyReference W β T ≤
        4 * β^2 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) +
          (β^2 / 2) * actualParisiFullSusceptibilitySquareExpected W β T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
  obtain ⟨hK, _hcount, hreach, hover, hcell⟩ := mesh_stop_geometry δ hδ T hT hscale
  have HI := actual_growing_information_error W β hβ δ hδ (growingQueryStop δ hδ T - 1) (by
    intro i hi
    rw [hK] at hi
    exact_mod_cast (hcell i hi).trans hscale)
  rw [hK] at HI
  have HO := actual_information_overshoot W β hβ T (growingQueryTime δ (growingQueryStop δ hδ T))
    (growingQueryStop_reaches δ hδ T)
  have HO' : actualParisiEntropyReference W β (growingQueryTime δ (growingQueryStop δ hδ T)) -
      actualParisiEntropyReference W β T ≤
        (β^2 / 2) * actualParisiFullSusceptibilitySquareExpected W β T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) := by
    calc
      _ ≤ (β^2 / 2) * actualParisiFullSusceptibilitySquareExpected W β T *
          ((growingQueryTime δ (growingQueryStop δ hδ T) : ℝ) - T) := HO.2
      _ ≤ (β^2 / 2) * actualParisiFullSusceptibilitySquareExpected W β T *
          ((δ : ℝ) * Real.exp ((T : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (by change meshTime δ (growingQueryStop δ hδ T) - T ≤ _; linarith)
          (mul_nonneg (by positivity) (actualParisiFullSusceptibilitySquareExpected_bounds W β T).1)
      _ = _ := by ring
  constructor <;> linarith [HI.1, HI.2, HO.1]

theorem actual_weighted_overshoot_scale (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (T : ℝ≥0) :
    actualParisiFullSusceptibilitySquareExpected W β T * (δ : ℝ) * Real.exp ((T : ℝ) / 4) ≤
      Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) * Real.exp (-(T : ℝ) / 4) :=
  weighted_overshoot_scale _ _ δ T (actual_square_profile_tail W β hβ T T.coe_nonneg)

end SKConstants.Completion.LQ
