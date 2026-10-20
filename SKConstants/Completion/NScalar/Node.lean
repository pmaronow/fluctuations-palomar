module

public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.NScalar.Profile
public import SKConstants.Completion.NScalar.IntervalIntegral

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.NScalar
open SKConstantsOAI.ZeroTemperatureSK LBase
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedLipschitzDrift.solution

theorem SusceptibilityProfileStatement_holds : Blueprint.SusceptibilityProfileStatement := by
  intro Ω _ W β hβ s t hs hst
  exact ⟨actual_susceptibility_antitone W β hβ hs (hs.trans hst) hst,
    susceptibility_exp_comparison W β hβ s t hs hst⟩

theorem MagnetizationIntegralStatement_holds : Blueprint.MagnetizationIntegralStatement := by
  intro Ω _ W β hβ s t hst
  simpa only [actualCurvatureDyadicIntervalSum, actualCurvatureProcess,
    Blueprint.dyadicTime, Real.toNNReal_coe] using
    actual_curvature_dyadic_interval_meanSquare_tendsto W β hβ s t hst

theorem SusceptibilityTailStatement_holds : Blueprint.SusceptibilityTailStatement := by
  intro Ω _ W β hβ
  refine ⟨terminalTailConstant β, terminalTailConstant_pos β, ?_⟩
  intro t ht
  simpa only [mul_div_assoc] using actual_susceptibility_global_tail W β hβ t ht

end SKConstants.Completion.NScalar
