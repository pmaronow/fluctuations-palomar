module

public import SKConstants.Completion.LBase.SquareDerivative
public import SKConstants.Completion.LBase.CurvatureIntervals

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LBase
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def ActualScalarProfileStatement (W : BrownianSystem Ω) (β : ℝ) : Prop :=
  Continuous (actualParisiFullSusceptibilityExpected W β) ∧
  Continuous (actualParisiFullSusceptibilitySquareExpected W β) ∧
  AntitoneOn (actualParisiFullSusceptibilityExpected W β) (Ici 0) ∧
  AntitoneOn (actualParisiFullSusceptibilitySquareExpected W β) (Ici 0) ∧
  ∀ t : ℝ, 0 ≤ t →
    0 < actualParisiFullSusceptibilitySquareExpected W β t ∧
    actualParisiFullSusceptibilitySquareExpected W β t ≤ 1 / β^2 ∧
    (actualParisiFullSusceptibilityExpected W β t)^2 ≤ actualParisiFullSusceptibilitySquareExpected W β t ∧
    actualParisiFullSusceptibilitySquareExpected W β t ≤ actualParisiFullSusceptibilityExpected W β t ∧
    actualParisiFullSusceptibilityExpected W β t ≤ 1 ∧
    actualParisiQueryRho W β t = β * Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β t) ∧
    HasDerivWithinAt (actualParisiFullSusceptibilityExpected W β)
      (-(cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β^2)) *
        actualParisiFullSusceptibilitySquareExpected W β t) (Ioi t) t ∧
    |-(cdf (parisiEquilibriumMeasure β : Measure ℝ) (t / β^2)) *
        actualParisiFullSusceptibilitySquareExpected W β t| ≤ actualParisiFullSusceptibilityExpected W β t ∧
    HasDerivWithinAt (actualParisiFullSusceptibilitySquareExpected W β)
      (actualSquareProfileRate W β t) (Ioi t) t ∧
    |actualSquareProfileRate W β t| ≤ 2 * actualParisiFullSusceptibilitySquareExpected W β t

theorem actual_scalar_profiles (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ActualScalarProfileStatement W β := by
  refine ⟨continuous_actualParisiFullSusceptibilityExpected W β,
    continuous_actualParisiFullSusceptibilitySquareExpected W β,
    actual_susceptibility_antitone W β hβ, LQ.actual_square_profile_antitone W β hβ, ?_⟩
  intro t ht
  exact ⟨actual_square_profile_pos W β hβ t ht,
    actual_square_profile_le_inverse_beta_sq W β hβ t ht,
    actualParisiFullSusceptibilityExpected_sq_le_squareExpected W β t,
    actual_square_profile_le_susceptibility W β t, actual_susceptibility_le_one W β t,
    LQ.actual_rho_eq W β hβ t ht,
    actual_susceptibility_hasDerivWithinAt_right W β hβ t ht,
    actual_susceptibility_derivative_bound W β t,
    actual_square_profile_hasDerivWithinAt_right W β hβ t ht,
    actual_square_profile_derivative_bound W β hβ t ht⟩

theorem actual_scalar_increment_variance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hST : S ≤ T) :
    (∫ w, (actualParisiMagnetizationIncrement W β S T w)^2 ∂W.law) =
      ∫ r in (S : ℝ)..T, actualParisiFullSusceptibilitySquareExpected W β r := by
  rw [actualParisiIncrement_secondMoment W β hβ S T hST]
  exact (actualParisiFullSusceptibilitySquareExpected_interval W β hβ S T hST).symm

theorem actual_scalar_foundation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ActualScalarProfileStatement W β ∧
    (∀ S T : ℝ≥0, S ≤ T →
      (∫ w, (actualParisiMagnetizationIncrement W β S T w)^2 ∂W.law) =
        ∫ r in (S : ℝ)..T, actualParisiFullSusceptibilitySquareExpected W β r) ∧
    (∀ t : ℝ≥0, t ≤ parisiEquilibriumPhysicalEndpoint β →
      actualParisiFullSusceptibilitySquareExpected W β t = 1 / β^2 ∧
      actualParisiQueryRho W β t = 1 ∧ actualParisiQuerySigma W β t = 0) ∧
    (∀ V : ℝ, (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ V →
      Real.log 2 - actualParisiEntropyReference W β V + β * actualParisiEnergyReference W β V =
        parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) -
          (β^2 / 4) * (actualParisiFullSusceptibilityExpected W β V)^2) ∧
    (∀ n : ℕ, 0 < n →
      (∫ A, Real.log (gibbsPartition β A) ∂skDisorderLaw n) / (n : ℝ) ≤
        parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ))) := by
  refine ⟨actual_scalar_profiles W β hβ, actual_scalar_increment_variance W β hβ, ?_,
    actualParisi_scalar_entropy_energy_identity W β hβ, (fun n hn => sk_expected_pressure_le_parisiEquilibrium n hn β)⟩
  intro t ht
  exact ⟨actualParisiFullSusceptibilitySquareExpected_pre W β hβ t ht,
    actualParisiQueryRho_eq_one_pre W β hβ t (NNReal.coe_le_coe.mpr ht),
    actualParisiQuerySigma_eq_zero_pre W β hβ t (NNReal.coe_le_coe.mpr ht)⟩

end SKConstants.Completion.LBase
