module

public import SKConstants.ScalarProcessSeedMixture
public import SKConstants.ParisiCDFDiffusion
public import SKConstants.ParisiEquilibriumEndpoint
public import SKConstants.ParisiBrownianSeedSymmetry

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKConstants
open SKConstantsOAI.SK.Analytic SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def parisiEquilibriumPhysicalEndpoint (β : ℝ) : ℝ≥0 :=
  Real.toNNReal (β^2*parisiEquilibriumSupportEndpoint β)

def actualParisiPreContinuationField (W : BrownianSystem Ω) (β : ℝ) : ℝ≥0 → Ω → ℝ :=
  ParisiFullSupport.finiteTemperatureCDFProcess W β
    (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1)

theorem measurable_actualParisiPreContinuationField
    (W : BrownianSystem Ω) (β : ℝ) (v : ℝ≥0) :
    Measurable (actualParisiPreContinuationField W β v) :=
  ParisiFullSupport.finiteTemperatureCDFProcess_measurable W β _ _ _ v

def actualParisiEndpointSeedLaw (W : BrownianSystem Ω) (β : ℝ) : Measure ℝ :=
  W.law.map (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β))

instance actualParisiEndpointSeedLaw_isProbability (W : BrownianSystem Ω) (β : ℝ) :
    IsProbabilityMeasure (actualParisiEndpointSeedLaw W β) := by
  let := W.isProbability
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_actualParisiPreContinuationField W β _).aemeasurable).mpr inferInstance

theorem actualParisiEndpointSeed_hasLaw (W : BrownianSystem Ω) (β : ℝ) :
    HasLaw (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β))
      (actualParisiEndpointSeedLaw W β) W.law :=
  ⟨(measurable_actualParisiPreContinuationField W β _).aemeasurable, rfl⟩

theorem actualParisiEndpointSeedLaw_neg (W : BrownianSystem Ω) (β : ℝ) :
    (actualParisiEndpointSeedLaw W β).map (fun x : ℝ => -x) =
      actualParisiEndpointSeedLaw W β :=
  finiteTemperatureCDFProcess_seedLaw_neg W β _ _ _ _

theorem actualParisiEndpointSeedLaw_tanh_integral_zero (W : BrownianSystem Ω) (β : ℝ) :
    (∫ z, Real.tanh z ∂actualParisiEndpointSeedLaw W β) = 0 :=
  scalarSeed_tanh_mean_eq_zero_of_symmetric _ (actualParisiEndpointSeedLaw_neg W β)

theorem parisiEquilibriumPhysicalEndpoint_coe (β : ℝ) (hβ : 1 < β) :
    (parisiEquilibriumPhysicalEndpoint β : ℝ) = β^2*parisiEquilibriumSupportEndpoint β := by
  rw [parisiEquilibriumPhysicalEndpoint, Real.coe_toNNReal]
  exact mul_nonneg (sq_nonneg _) (parisiEquilibriumSupportEndpoint_spec β hβ).1.1.le

def actualParisiSeedContinuationLaw (W : BrownianSystem Ω) (β : ℝ)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [SFinite P] : Measure (ℝ × (Bool × A)) :=
  scalarSeedHiddenBrownianLaw (actualParisiEndpointSeedLaw W β) P

instance actualParisiSeedContinuationLaw_isProbability (W : BrownianSystem Ω) (β : ℝ)
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (actualParisiSeedContinuationLaw W β P) := by
  unfold actualParisiSeedContinuationLaw
  infer_instance

theorem actualParisiSeedContinuationLaw_hiddenSign_mean
    (W : BrownianSystem Ω) (β : ℝ) {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] :
    (∫ u, scalarHiddenSign u.2.1 ∂actualParisiSeedContinuationLaw W β P) = 0 := by
  unfold actualParisiSeedContinuationLaw
  rw [scalarSeedHiddenBrownianLaw_hiddenSign_mean,
    actualParisiEndpointSeedLaw_tanh_integral_zero]

theorem actualParisiSeedContinuationLaw_hiddenSign_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] :
    HasSubgaussianMGF (fun u : ℝ × (Bool × A) => scalarHiddenSign u.2.1) 1
      (actualParisiSeedContinuationLaw W β P) :=
  scalarSeedHiddenSign_hasSubgaussianMGF_of_symmetric _ P (actualParisiEndpointSeedLaw_neg W β)

end SKConstants
