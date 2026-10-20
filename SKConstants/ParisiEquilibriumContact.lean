module
public import SKConstants.ParisiEquilibriumEndpoint

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.SK.Analytic

theorem parisiEquilibrium_zero_mem_support (β : ℝ) (hβ : β ≠ 0) :
    0 ∈ (parisiEquilibriumMeasure β : Measure ℝ).support :=
  scalarCDFParisi_zero_mem_support hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2

theorem parisiEquilibrium_overlap_on_support (β : ℝ) (hβ : β ≠ 0)
    (q : ℝ) (hq : q ∈ (parisiEquilibriumMeasure β : Measure ℝ).support) :
    scalarCDFOverlap β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) q = q :=
  scalarCDFParisi_overlap_on_support hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2 hq

theorem parisiEquilibrium_overlap_ae (β : ℝ) (hβ : β ≠ 0) :
    ∀ᵐ q ∂(parisiEquilibriumMeasure β : Measure ℝ),
      scalarCDFOverlap β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) q = q :=
  scalarCDFParisi_overlap_eq_ae hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2

theorem parisiEquilibrium_origin_stability (β : ℝ) (hβ : β ≠ 0) :
    β^2 * (scalarCDFHessian β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) 0 1 0)^2 ≤ 1 :=
  scalarCDFParisi_origin_stability hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2

theorem parisiEquilibrium_AT_at_zero (β : ℝ) (hβ : β ≠ 0) :
    β^2 * scalarCDFSusceptibilitySquareAverage β
      (cdf (parisiEquilibriumMeasure β : Measure ℝ)) 0 ≤ 1 :=
  ParisiSupportAT.scalarCDFParisi_AT_at_zero hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2

end SKConstants
