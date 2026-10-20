module

public import SKConstants.ParisiCDFPotentialExpectation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

theorem parisiEquilibrium_potential_expectation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1)
    {V : ℝ} (hV : V∈Icc 0 (β^2*parisiEquilibriumSupportEndpoint β)) :
    (∫ w, parisiPhysicalValue β (parisiEquilibriumMeasure β) V
      (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
        (Real.toNNReal V) w) ∂W.law)=
      parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0+
        (1/2:ℝ)*(∫ v in 0..V, cdf (parisiEquilibriumMeasure β:Measure ℝ) (v/β^2)*(v/β^2)) := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let T := (Q+1)/2
  have hp : 0<β := zero_lt_one.trans hβ
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hQT : Q<T := by dsimp [T]; linarith [hQ.2]
  have hT0 : 0≤T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T<1 := by dsimp [T]; linarith [hQ.2]
  have hq {v : ℝ} (hv : v∈Icc 0 (β^2*Q)) : v/β^2∈Icc (0:ℝ) T :=
    ⟨div_nonneg hv.1 (sq_nonneg β), ((div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
      (by simpa only [mul_comm] using hv.2)).trans hQT.le⟩
  have hVQ : V/β^2≤Q := (div_le_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
    (by simpa only [mul_comm] using hV.2)
  have H := physicalCDFPotentialExpected_integral W β α ha h1 hp.ne' hT0 hT1 V hV.1
    (hVQ.trans_lt hQT)
  have HE : (∫ w, parisiPhysicalValue β (parisiEquilibriumMeasure β) V
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal V) w) ∂W.law)=
      physicalCDFPotentialExpected W β α ha h1 T V := by
    unfold physicalCDFPotentialExpected physicalCDFPotential compactCDFValue parisiPhysicalValue
    simp_rw [parisiCDFValue_eq_upstream,cdfStripTime_eq (hq hV)]
    rfl
  rw [HE,H]
  have Hz : parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0=scalarCDFValue β α 0 1 0 := by
    simp only [parisiPhysicalValue,zero_div,sub_zero,Real.toNNReal_one,parisiCDFValue_eq_upstream]
    rfl
  rw [Hz]
  congr 2
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hV.1] at hv
  have hvQ : v∈Icc 0 (β^2*Q) := ⟨hv.1,hv.2.trans hV.2⟩
  have HM := (parisiEquilibrium_physicalBrownian_moments W β hβ ha h1 hvQ).1
  have he : physicalCDFJetSquareMoment W β α ha h1 T 0 v=v/β^2 := by
    simpa only [physicalCDFJetSquareMoment,compactCDFJet,iteratedDeriv_zero,compactCDFGradient,
      cdfStripTime_eq (hq hvQ)] using HM
  change compactCDFCoefficient α T (v/β^2)*physicalCDFJetSquareMoment W β α ha h1 T 0 v=
    α (v/β^2)*(v/β^2)
  rw [he,compactCDFCoefficient,cdfStripTime_eq (hq hvQ)]

end SKConstants
