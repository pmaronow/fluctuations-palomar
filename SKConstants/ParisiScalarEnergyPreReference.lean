module

public import SKConstants.ParisiScalarEnergyMomentIdentification
public import SKConstants.ParisiFullVarianceIntegral
public import SKConstants.ParisiEquilibriumEntropyDissipation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

def actualParisiEndpointEntropy (W : BrownianSystem Ω) (β : ℝ) : ℝ :=
  ∫ w,binarySpinEntropy (Real.tanh
    (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β) w)) ∂W.law

lemma beta_sqrt_inverse_sq (β : ℝ) (hβ : 0<β) : β*Real.sqrt (1/β^2)=1 := by
  have hsq : (β*Real.sqrt (1/β^2))^2=1 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    field_simp
  have hp : 0≤β*Real.sqrt (1/β^2) := mul_nonneg hβ.le (Real.sqrt_nonneg _)
  nlinarith

theorem actualParisiEnergyReference_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) :
    β*actualParisiEnergyReference W β (parisiEquilibriumPhysicalEndpoint β)=
      ∫ v in 0..(parisiEquilibriumPhysicalEndpoint β:ℝ),actualParisiFullSusceptibilityExpected W β v := by
  unfold actualParisiEnergyReference
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (parisiEquilibriumPhysicalEndpoint β).coe_nonneg] at hv
  have hvt : v.toNNReal≤parisiEquilibriumPhysicalEndpoint β := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal v hv.1]
    exact hv.2
  have HR := actualParisiFullSusceptibilitySquareExpected_pre W β hβ v.toNNReal hvt
  rw [Real.coe_toNNReal v hv.1] at HR
  dsimp only
  rw [HR,actualParisiQueryRho_eq_one_pre W β hβ v hv.2,mul_one]
  rw [←mul_assoc,beta_sqrt_inverse_sq β (zero_lt_one.trans hβ),one_mul]

theorem actualParisiEntropyReference_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z,cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1) :
    actualParisiEntropyReference W β (parisiEquilibriumPhysicalEndpoint β)=
      Real.log 2-actualParisiEndpointEntropy W β := by
  let V : ℝ := parisiEquilibriumPhysicalEndpoint β
  have hV : V∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β) :=
    ⟨(parisiEquilibriumPhysicalEndpoint β).coe_nonneg,by dsimp [V];rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]⟩
  have HE := parisiEquilibrium_entropy_dissipation W β hβ ha h1 hV
  have HL : (∫ w,binarySpinEntropy
      (scalarCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (V/β^2)
        (Real.toNNReal (1-V/β^2))
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
          (Real.toNNReal V) w)) ∂W.law)=actualParisiEndpointEntropy W β := by
    unfold actualParisiEndpointEntropy
    apply integral_congr_ae
    filter_upwards [] with w
    have HT := congrFun (actualParisiFullMagnetization_eq_tanh_after_support β hβ V
      (by rw [←parisiEquilibriumPhysicalEndpoint_coe β hβ]))
      (actualParisiFullScalarProcess W β (Real.toNNReal V) w)
    simp only [actualParisiFullMagnetization,cdfTimeClamp_eq (parisiPhysicalTime_mem_unit β hβ hV),
      actualParisiFullScalarProcess,actualParisiFullScalarDrift,finiteTemperatureCDFProcess,
      V,Real.toNNReal_coe] at HT ⊢
    rw [HT]
  rw [HL] at HE
  have HI : (∫ v in 0..V,actualParisiFullEntropyRateExpected W β v)=
      ∫ v in 0..V,∫ w,(scalarCDFHessian β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (v/β^2)
        (Real.toNNReal (1-v/β^2))
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
          (Real.toNNReal v) w))^2/
        (1-(scalarCDFGradient β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) (v/β^2)
          (Real.toNNReal (1-v/β^2))
          (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
            (Real.toNNReal v) w))^2) ∂W.law := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hV.1] at hv
    exact actualParisiFullEntropyRateExpected_pre W β hβ ha h1 ⟨hv.1,hv.2.trans hV.2⟩
  have HJ : actualParisiEntropyReference W β V=(1/2:ℝ)*(∫ v in 0..V,actualParisiFullEntropyRateExpected W β v) := by
    unfold actualParisiEntropyReference
    congr 1
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hV.1] at hv
    dsimp only
    rw [actualParisiQueryRho_eq_one_pre W β hβ v hv.2,one_pow,one_mul]
  rw [HJ,HI]
  linarith

theorem actualParisiEnergyReference_endpoint_balance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z,cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1) :
    β*actualParisiEnergyReference W β (parisiEquilibriumPhysicalEndpoint β)+
      actualParisiEndpointEntropy W β=
        parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
          (β^2/4)*(1-parisiEquilibriumSupportEndpoint β)^2 := by
  rw [actualParisiEnergyReference_pre W β hβ]
  have HI : (∫ v in 0..(parisiEquilibriumPhysicalEndpoint β:ℝ),actualParisiFullSusceptibilityExpected W β v)=
      ∫ v in 0..(β^2*parisiEquilibriumSupportEndpoint β),parisiPreSusceptibilityExpected W β ha h1 v := by
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by rw [←parisiEquilibriumPhysicalEndpoint_coe β hβ];exact (parisiEquilibriumPhysicalEndpoint β).coe_nonneg)] at hv
    exact actualParisiFullSusceptibilityExpected_pre W β hβ ha h1 hv
  rw [HI]
  simpa only [actualParisiEndpointEntropy,actualParisiFullScalarProcess,actualParisiFullScalarDrift,
    finiteTemperatureCDFProcess,←parisiEquilibriumPhysicalEndpoint_coe β hβ,Real.toNNReal_coe] using
    parisiEquilibrium_entropy_energy_identity W β hβ ha h1

end SKConstants
