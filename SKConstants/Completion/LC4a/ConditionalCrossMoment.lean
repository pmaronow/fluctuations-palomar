module
public import SKConstants.Completion.LC4a.ReplayInformation
public import SKConstants.ParisiFullRowSecondMoment
public import SKConstants.ParisiScalarEnergyPreReference
public import SKConstants.ScalarOrthogonalWeightedBrownian
public import SKConstants.Completion.LC4a.ScalarEntropy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

lemma sigma_mul_spinLinkCoefficient (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (b : Bool) (v y : ℝ) :
    actualParisiQuerySigma W β v * actualParisiSpinLinkCoefficient β b v y =
      actualParisiQuerySigma W β v *
        (scalarHiddenSign b - actualParisiFullMagnetization β v y) := by
  by_cases hv : v ≤ (parisiEquilibriumPhysicalEndpoint β : ℝ)
  · rw [actualParisiQuerySigma_eq_zero_pre W β hβ v hv, zero_mul, zero_mul]
  · have hv' : β^2 * parisiEquilibriumSupportEndpoint β ≤ v := by
      rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
      exact (le_of_not_ge hv)
    rw [actualParisiSpinLinkCoefficient_eq_signed_defect_after_support β hβ b v y hv',
      actualParisiFullMagnetization_eq_tanh_after_support β hβ v hv']

def actualSigmaSquareStieltjes (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    StieltjesFunction ℝ where
  toFun v := (actualParisiQuerySigma W β v)^2
  mono' := fun _ _ hab => pow_le_pow_left₀ (Real.sqrt_nonneg _)
    (actualParisiQuerySigma_monotone W β hβ hab) 2
  right_continuous' := fun _ =>
    ((continuous_actualParisiQuerySigma W β).pow 2).continuousAt.continuousWithinAt

lemma continuous_actualSigmaSquareStieltjes (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Continuous (actualSigmaSquareStieltjes W β hβ) :=
  (continuous_actualParisiQuerySigma W β).pow 2

lemma sigmaSquare_profile_integral_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) :
    (∫ v in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β v)^2 *
      actualParisiFullSusceptibilityExpected W β v) =
      ∫ v in (parisiEquilibriumPhysicalEndpoint β : ℝ)..(V : ℝ),
        (actualParisiQuerySigma W β v)^2 * actualParisiFullSusceptibilityExpected W β v := by
  let a := parisiEquilibriumPhysicalEndpoint β
  let f := fun v => (actualParisiQuerySigma W β v)^2 * actualParisiFullSusceptibilityExpected W β v
  have hc : Continuous f := ((continuous_actualParisiQuerySigma W β).pow 2).mul
    (continuous_actualParisiFullSusceptibilityExpected W β)
  have hz : (∫ v in (0 : ℝ)..(a : ℝ), f v) = 0 := by
    calc
      _ = ∫ _v in (0 : ℝ)..(a : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le a.coe_nonneg] at hv
        dsimp only [f]
        rw [actualParisiQuerySigma_eq_zero_pre W β hβ v hv.2, zero_pow (by norm_num), zero_mul]
      _ = 0 := by simp
  have hi (s t : ℝ) : IntervalIntegrable f volume s t := hc.intervalIntegrable s t
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a V)
  simpa only [hz, zero_add] using hs.symm

namespace Conditional

def LC1StieltjesCrossMomentStatement (W : BrownianSystem Ω) (β : ℝ) : Prop :=
  ∀ (s t H : ℝ≥0), s ≤ t → t ≤ H →
    ∀ (f : StieltjesFunction ℝ), Continuous f →
    ∀ (F : ScalarContinuousPath s → ℝ), Measurable F →
    ∀ (C : ℝ), (∀ p, |F p| ≤ C) →
      (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) *
        actualParisiMagnetizationObservable W β H w *
        (scalarGlobalStieltjesWeightedProcess f W.driver t w -
          scalarGlobalStieltjesWeightedProcess f W.driver s w) ∂W.law) =
        ∫ u in (s : ℝ)..(t : ℝ), f u *
          (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) s w) *
            actualParisiFullCurvature β u
              (actualParisiFullScalarProcess W β u.toNNReal w) ∂W.law)

theorem sigmaSquare_terminal_covariance_of_LC1
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (hLC1 : LC1StieltjesCrossMomentStatement W β) (V : ℝ≥0) :
    (∫ w, actualParisiMagnetizationObservable W β V w *
      scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
      ∂W.law) =
      ∫ v in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β v)^2 *
        actualParisiFullSusceptibilityExpected W β v := by
  have h := hLC1 0 V V bot_le le_rfl (actualSigmaSquareStieltjes W β hβ)
    (continuous_actualSigmaSquareStieltjes W β hβ) (fun _ => 1) measurable_const 1
    (fun _ => by norm_num)
  have hzero (w : Ω) : scalarGlobalStieltjesWeightedProcess
      (actualSigmaSquareStieltjes W β hβ) W.driver 0 w = 0 := by
    simp only [scalarGlobalStieltjesWeightedProcess, actualSigmaSquareStieltjes, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero]
    rw [actualParisiQuerySigma_eq_zero_pre W β hβ 0
      (parisiEquilibriumPhysicalEndpoint β).coe_nonneg]
    simp
  simp_rw [hzero] at h
  simpa only [sub_zero, one_mul, NNReal.coe_zero,
    actualSigmaSquareStieltjes, actualParisiFullSusceptibilityExpected] using h

theorem scalar_information_balance_of_LC1
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (hLC1 : LC1StieltjesCrossMomentStatement W β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    (∫ u, Real.log (actualParisiFullTerminalSpinDensity β W V u)
      ∂actualParisiFullTerminalSpinLaw β W V) -
      (1 / 2 : ℝ) * (∫ w, actualParisiMagnetizationObservable W β V w *
        scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
        ∂W.law) = actualParisiEntropyReference W β V := by
  rw [(actualTerminalLink_log_mean W β V).2,
    sigmaSquare_terminal_covariance_of_LC1 W β hβ hLC1 V,
    sigmaSquare_profile_integral_post W β hβ V,
    actualTerminalEntropy_reference_balance W β hβ V hV]
  ring

end Conditional
end SKConstants.Completion.LC4a
