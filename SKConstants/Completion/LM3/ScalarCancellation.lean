module
public import SKConstants.Completion.LC4a.ConditionalCrossMoment
public import SKConstants.Completion.LC1.StieltjesCrossMoment

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM3
open SKConstantsOAI.ZeroTemperatureSK LC4a
variable {Ω : Type*} [MeasurableSpace Ω]

theorem lc1StieltjesCrossMoment (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    Conditional.LC1StieltjesCrossMomentStatement W β := by
  intro s t H hst htH f hf F hF C hC
  have h := LC1.actualFullProcess_stieltjes_cross_moment_test W β hβ f hf
    s t H hst htH F hF ⟨|C|, abs_nonneg C⟩
    (fun p => (hC p).trans (le_abs_self C))
  refine h.trans ?_
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (NNReal.coe_le_coe.mpr hst)] at hu
  dsimp only
  rw [Real.coe_toNNReal u (s.coe_nonneg.trans hu.1)]

theorem sigmaSquare_terminal_covariance
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∫ w, actualParisiMagnetizationObservable W β V w *
      scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
      ∂W.law) =
      ∫ v in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β v)^2 *
        actualParisiFullSusceptibilityExpected W β v :=
  Conditional.sigmaSquare_terminal_covariance_of_LC1 W β hβ
    (lc1StieltjesCrossMoment W β hβ) V

theorem scalar_information_balance
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (hV : parisiEquilibriumPhysicalEndpoint β ≤ V) :
    (∫ u, Real.log (actualParisiFullTerminalSpinDensity β W V u)
      ∂actualParisiFullTerminalSpinLaw β W V) -
      (1 / 2 : ℝ) * (∫ w, actualParisiMagnetizationObservable W β V w *
        scalarGlobalStieltjesWeightedProcess (actualSigmaSquareStieltjes W β hβ) W.driver V w
        ∂W.law) = actualParisiEntropyReference W β V :=
  Conditional.scalar_information_balance_of_LC1 W β hβ
    (lc1StieltjesCrossMoment W β hβ) V hV

end SKConstants.Completion.LM3
