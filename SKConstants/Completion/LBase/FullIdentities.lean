module

public import SKConstants.Completion.LBase.Foundation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem actual_energy_eq_beta_profile_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ) (hV : 0 ≤ V) :
    actualParisiEnergyReference W β V = β *
      (∫ t in (0 : ℝ)..V, actualParisiFullSusceptibilitySquareExpected W β t *
        actualParisiFullSusceptibilityExpected W β t) := by
  unfold actualParisiEnergyReference
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hV] at ht
  dsimp only
  rw [LQ.actual_rho_eq W β hβ t ht.1]
  have hs := Real.sq_sqrt (actualParisiFullSusceptibilitySquareExpected_bounds W β t).1
  calc
    _ = β * (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t))^2 *
        actualParisiFullSusceptibilityExpected W β t := by ring
    _ = _ := by rw [hs]; ring

theorem actual_integrated_variance_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..T, actualParisiFullSusceptibilitySquareExpected W β t) =
      ∫ w, (actualParisiMagnetizationObservable W β T w)^2 ∂W.law ∧
    (∫ t in (0 : ℝ)..T, actualParisiFullSusceptibilitySquareExpected W β t) ≤ 1 := by
  refine ⟨actual_curvature_energy_eq_terminal_secondMoment W β hβ T, ?_⟩
  rw [actual_curvature_energy_eq_terminal_secondMoment W β hβ T]
  have H := integral_mono (memLp_actualMagnetization W β T).integrable_sq (integrable_const (1 : ℝ))
    (fun w => by
      have hb := actualParisiMagnetizationObservable_abs_le W β T w
      exact (sq_le_one_iff_abs_le_one _).mpr hb)
  simpa only [integral_const, probReal_univ, one_smul] using H

theorem actual_post_susceptibility_eq_defect (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) (hT : parisiEquilibriumPhysicalEndpoint β ≤ T) :
    actualParisiFullSusceptibilityExpected W β T = 1 - actualParisiFullOverlap W β T := by
  let v := T - parisiEquilibriumPhysicalEndpoint β
  have hO := actualParisiFullOverlap_post W β hβ v
  have hP := actualParisiFullSusceptibilityExpected_post W β hβ v v.coe_nonneg
  have hv : parisiEquilibriumPhysicalEndpoint β + v = T := add_tsub_cancel_of_le hT
  have hvr : (parisiEquilibriumPhysicalEndpoint β : ℝ) + (v : ℝ) = (T : ℝ) := by exact_mod_cast hv
  rw [hv] at hO
  rw [hvr] at hP
  linarith

theorem actual_post_entropy_rate_eq_susceptibility (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℝ) (ht : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ t) :
    actualParisiFullEntropyRateExpected W β t = actualParisiFullSusceptibilityExpected W β t := by
  have hv := sub_nonneg.mpr ht
  have hK := actualParisiFullEntropyRateExpected_post W β hβ _ hv
  have hP := actualParisiFullSusceptibilityExpected_post W β hβ _ hv
  rw [add_sub_cancel] at hK hP
  exact hK.trans hP.symm

theorem actual_scalar_BV_weights (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ f g : StieltjesFunction ℝ, Continuous f ∧ Continuous g ∧
      (∀ t : ℝ, f t = -actualParisiQueryRho W β t ∧ g t = actualParisiQuerySigma W β t) ∧
      (∀ t : ℝ, (actualParisiQueryRho W β t)^2 + (actualParisiQuerySigma W β t)^2 = 1) := by
  exact ⟨actualParisiNegativeRhoStieltjes W β hβ, actualParisiSigmaStieltjes W β hβ,
    continuous_actualParisiNegativeRhoStieltjes W β hβ, continuous_actualParisiSigmaStieltjes W β hβ,
    fun _ => ⟨rfl, rfl⟩, actualParisiQueryRhoSigma_unit W β hβ⟩

end SKConstants.Completion.LBase
