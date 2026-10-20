module

public import SKConstants.ParisiUpstreamBridge
public import SKConstants.ParisiGOEBridge
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFMinimizer
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CommonMinimizer

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

def parisiDyadicSteps (β : ℝ) (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    List (ℝ × ℝ≥0 × ℝ) :=
  (SKConstantsOAI.SK.Analytic.dyadicIntervals α n s t).map
    (fun p => (0, parisiUpstreamVariance β p.2, p.1))

def parisiCDFValue (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  limUnder atTop (fun n => parisiGaussianIterate (parisiDyadicSteps β α n s t) x)

theorem parisiCDFValue_eq_upstream (β : ℝ) (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) :
    parisiCDFValue β α s t = SKConstantsOAI.SK.Analytic.scalarCDFValue β α s t := by
  funext x
  simp only [parisiCDFValue, parisiDyadicSteps,
    parisiGaussianIterate_eq_upstream_timeChain,
    SKConstantsOAI.SK.Analytic.scalarCDFValue, SKConstantsOAI.SK.Analytic.dyadicScalar]

theorem parisiDyadic_uniform_convergence (β : ℝ) (α : ℝ → ℝ)
    (hα : ∀ s, α s ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => parisiGaussianIterate (parisiDyadicSteps β α n s t))
      (parisiCDFValue β α s t) atTop := by
  simp only [parisiDyadicSteps, parisiGaussianIterate_eq_upstream_timeChain,
    parisiCDFValue_eq_upstream]
  exact SKConstantsOAI.SK.Analytic.dyadicScalar_value_uniform β hα hmono s t ht

theorem parisiCDFValue_spatial_derivatives (β : ℝ) (α : ℝ → ℝ)
    (hα : ∀ s, α s ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    (∀ x, HasDerivAt (parisiCDFValue β α s t)
      (SKConstantsOAI.SK.Analytic.scalarCDFGradient β α s t x) x) ∧
    (∀ x, HasDerivAt (SKConstantsOAI.SK.Analytic.scalarCDFGradient β α s t)
      (SKConstantsOAI.SK.Analytic.scalarCDFHessian β α s t x) x) ∧
    (∀ x, |SKConstantsOAI.SK.Analytic.scalarCDFGradient β α s t x| ≤ 1 ∧
      0 ≤ SKConstantsOAI.SK.Analytic.scalarCDFHessian β α s t x ∧
      SKConstantsOAI.SK.Analytic.scalarCDFHessian β α s t x ≤
        1 - (SKConstantsOAI.SK.Analytic.scalarCDFGradient β α s t x)^2) := by
  rw [parisiCDFValue_eq_upstream]
  exact ⟨SKConstantsOAI.SK.Analytic.scalarCDFValue_hasDerivAt β hα hmono s t ht,
    SKConstantsOAI.SK.Analytic.scalarCDFGradient_hasDerivAt β hα hmono s t ht,
    SKConstantsOAI.SK.Analytic.scalarCDF_derivative_bounds β hα hmono s t ht⟩

def parisiContinuumFunctional (β : ℝ) (α : ℝ → ℝ) : ℝ :=
  parisiCDFValue β α 0 1 0 - (β^2/2) * ∫ s in Icc (0 : ℝ) 1, s * α s

theorem parisiContinuumFunctional_eq_upstream (β : ℝ) (α : ℝ → ℝ) :
    parisiContinuumFunctional β α = SKConstantsOAI.SK.Analytic.scalarCDFParisi β α := by
  simp only [parisiContinuumFunctional, parisiCDFValue_eq_upstream,
    SKConstantsOAI.SK.Analytic.scalarCDFParisi]

theorem exists_parisiContinuum_minimizer (β : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1 ∧
      parisiContinuumFunctional β (cdf (μ : Measure ℝ)) =
        SKConstantsOAI.SK.Analytic.finiteParisiInf β ∧
      ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
        parisiContinuumFunctional β (cdf (μ : Measure ℝ)) ≤
          parisiContinuumFunctional β (cdf (ν : Measure ℝ)) := by
  simpa only [parisiContinuumFunctional_eq_upstream] using
    SKConstantsOAI.SK.Analytic.exists_scalarCDFParisi_minimizer β

def parisiEquilibriumMeasure (β : ℝ) : ProbabilityMeasure ℝ :=
  Classical.choose (SKConstantsOAI.SK.Analytic.exists_scalarCDFParisi_minimizer_full_susceptibility β)

theorem parisiEquilibriumMeasure_spec (β : ℝ) :
    (parisiEquilibriumMeasure β : Measure ℝ) (Icc (0 : ℝ) 1) = 1 ∧
      parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) =
        SKConstantsOAI.SK.Analytic.finiteParisiInf β ∧
      ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
        parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) ≤
          parisiContinuumFunctional β (cdf (ν : Measure ℝ)) := by
  have H := Classical.choose_spec
    (SKConstantsOAI.SK.Analytic.exists_scalarCDFParisi_minimizer_full_susceptibility β)
  have hmin : SKConstantsOAI.SK.Analytic.scalarCDFParisi β
      (cdf (parisiEquilibriumMeasure β : Measure ℝ)) = SKConstantsOAI.SK.Analytic.finiteParisiInf β := H.2.1
  refine ⟨H.1, ?_, ?_⟩
  · rw [parisiContinuumFunctional_eq_upstream]
    exact H.2.1
  · intro ν hν
    rw [parisiContinuumFunctional_eq_upstream, parisiContinuumFunctional_eq_upstream, hmin]
    exact SKConstantsOAI.SK.Analytic.finiteParisiInf_le_scalarCDFParisi β (cdf (ν : Measure ℝ))
      (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
      (SKConstantsOAI.SK.Analytic.supported_probability_cdf_one ν hν)

theorem parisiEquilibriumMeasure_full_susceptibility (β : ℝ) :
    ∀ r ∈ Icc (0 : ℝ) 1,
      SKConstantsOAI.SK.Analytic.scalarCDFSusceptibilityAverage β
        (cdf (parisiEquilibriumMeasure β : Measure ℝ)) r =
        1 - ∫ x, SKConstantsOAI.SK.Analytic.scalarCDFOverlap β
          (cdf (parisiEquilibriumMeasure β : Measure ℝ)) (max x r)
          ∂(parisiEquilibriumMeasure β : Measure ℝ) :=
  (Classical.choose_spec
    (SKConstantsOAI.SK.Analytic.exists_scalarCDFParisi_minimizer_full_susceptibility β)).2.2

theorem sk_expected_pressure_eq_upstream (n : ℕ) (β : ℝ) :
    (∫ W, Real.log (gibbsPartition β W) ∂skDisorderLaw n) / (n : ℝ) =
      SKConstantsOAI.SK.Analytic.quenchedPressure β n := by
  simpa only [SKConstantsOAI.SK.Analytic.quenchedPressure, SKConstantsOAI.SK.logPartition] using
    ParisiGOEBridge.expected_pressure_eq_upstream_model n β

theorem sk_expected_pressure_le_parisiEquilibrium (n : ℕ) (hn : 0 < n) (β : ℝ) :
    (∫ W, Real.log (gibbsPartition β W) ∂skDisorderLaw n) / (n : ℝ) ≤
      parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) := by
  rw [sk_expected_pressure_eq_upstream, (parisiEquilibriumMeasure_spec β).2.1]
  exact SKConstantsOAI.SK.Analytic.quenched_le_finiteParisiInf hn β

theorem sk_expected_pressure_tendsto_parisiEquilibrium {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => (∫ W, Real.log (gibbsPartition β W) ∂skDisorderLaw n) / (n : ℝ))
      atTop (𝓝 (parisiContinuumFunctional β
        (cdf (parisiEquilibriumMeasure β : Measure ℝ)))) := by
  simp only [sk_expected_pressure_eq_upstream, (parisiEquilibriumMeasure_spec β).2.1]
  exact SKConstantsOAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf hβ

end SKConstants
