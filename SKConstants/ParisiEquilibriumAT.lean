module
public import SKConstants.ParisiCDFBrownianLaw
public import SKConstants.ParisiEquilibriumContact

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic

theorem scalarCDFParisi_AT_on_support_actualBrownian
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    {β : ℝ} (hβ : 0 < β) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ:Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ:Measure ℝ))=finiteParisiInf β)
    {q : ℝ} (hq : q ∈ (μ:Measure ℝ).support) :
    β^2*scalarCDFSusceptibilitySquareAverage β (cdf (μ:Measure ℝ)) q ≤ 1 := by
  apply ParisiSupportAT.scalarCDFParisi_AT_on_support_of_overlap_derivatives hβ.ne' μ hμ hmin _ hq
  intro r hr
  exact ParisiFullSupport.scalarCDFOverlap_hasDerivAt_actual W β hβ _
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one μ hμ) hr

theorem parisiEquilibrium_AT_on_support
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 0 < β) {q : ℝ}
    (hq : q ∈ (parisiEquilibriumMeasure β:Measure ℝ).support) :
    β^2*scalarCDFSusceptibilitySquareAverage β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) q ≤ 1 :=
  scalarCDFParisi_AT_on_support_actualBrownian W hβ _
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2 hq

theorem parisiEquilibrium_AT_ae
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ q ∂(parisiEquilibriumMeasure β:Measure ℝ),
      β^2*scalarCDFSusceptibilitySquareAverage β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) q ≤ 1 := by
  filter_upwards [(parisiEquilibriumMeasure β:Measure ℝ).support_mem_ae] with q hq
  exact parisiEquilibrium_AT_on_support W β hβ hq

end SKConstants
