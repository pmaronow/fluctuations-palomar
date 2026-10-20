module

public import SKConstants.ParisiScalarEnergyPostReference

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualParisi_scalar_entropy_energy_identity_shifted
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (S : ℝ) (hS : 0≤S) :
    Real.log 2-actualParisiEntropyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S)+
      β*actualParisiEnergyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S)=
        parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
          (β^2/4)*(actualParisiContinuationP W β S)^2 := by
  let ha : ∀ z,cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1 :=
    fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1 :=
    supported_probability_cdf_one (parisiEquilibriumMeasure β) (parisiEquilibriumMeasure_upstream_spec β).1
  let I := ∫ v in 0..S,actualParisiContinuationR W β v*actualParisiContinuationP W β v
  have HB : (β^2/2)*I=(β^2/4)*
      ((1-parisiEquilibriumSupportEndpoint β)^2-(actualParisiContinuationP W β S)^2) := by
    dsimp [I]
    rw [actualParisiContinuationRP_square_balance W β hβ S hS,actualParisiContinuationP_zero W β hβ]
    ring
  rw [actualParisiEntropyReference_post_increment W β hβ S hS,
    actualParisiEnergyReference_post_increment W β hβ S hS,
    actualParisiEntropyReference_pre W β hβ ha h1]
  change Real.log 2-(Real.log 2-actualParisiEndpointEntropy W β+(β^2/2)*I)+
    β*(actualParisiEnergyReference W β (parisiEquilibriumPhysicalEndpoint β)+β*I)=_
  calc
    _ = (β*actualParisiEnergyReference W β (parisiEquilibriumPhysicalEndpoint β)+
        actualParisiEndpointEntropy W β)+(β^2/2)*I := by ring
    _ = _ := by
      rw [actualParisiEnergyReference_endpoint_balance W β hβ ha h1,HB]
      ring

theorem actualParisi_scalar_entropy_energy_identity
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (V : ℝ)
    (hV : (parisiEquilibriumPhysicalEndpoint β:ℝ)≤V) :
    Real.log 2-actualParisiEntropyReference W β V+β*actualParisiEnergyReference W β V=
      parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
        (β^2/4)*(actualParisiFullSusceptibilityExpected W β V)^2 := by
  have hS := sub_nonneg.mpr hV
  have H := actualParisi_scalar_entropy_energy_identity_shifted W β hβ
    (V-(parisiEquilibriumPhysicalEndpoint β:ℝ)) hS
  have HP := actualParisiFullSusceptibilityExpected_post W β hβ
    (V-(parisiEquilibriumPhysicalEndpoint β:ℝ)) hS
  rw [add_sub_cancel] at H HP
  rw [←HP] at H
  exact H

end SKConstants
