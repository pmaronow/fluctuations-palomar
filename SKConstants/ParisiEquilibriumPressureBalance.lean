module

public import SKConstants.ParisiEquilibriumTerminalBalance

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

theorem parisiEquilibrium_physical_pressure_cancellation (β : ℝ) (hβ : 1<β) :
    parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 0-
      (1/2:ℝ)*(∫ v in 0..(β^2*parisiEquilibriumSupportEndpoint β),
        cdf (parisiEquilibriumMeasure β:Measure ℝ) (v/β^2)*(v/β^2))-
      (β^2-β^2*parisiEquilibriumSupportEndpoint β)/2=
    parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
      (β^2/4)*(1-parisiEquilibriumSupportEndpoint β)^2 := by
  let μ := parisiEquilibriumMeasure β
  let α := cdf (μ:Measure ℝ)
  let Q := parisiEquilibriumSupportEndpoint β
  let V := β^2*Q
  have hp : 0<β := zero_lt_one.trans hβ
  have hb : β^2≠0 := pow_ne_zero 2 hp.ne'
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hV0 : 0≤V := mul_nonneg (sq_nonneg β) hQ.1.le
  have hVb : V≤β^2 := mul_le_of_le_one_right (sq_nonneg β) hQ.2.le
  have HF : parisiContinuumFunctional β α=parisiPhysicalValue β μ 0 0-
      (1/2:ℝ)*(∫ v in 0..β^2, α (v/β^2)*(v/β^2)) := by
    rw [parisiContinuumFunctional_eq_physical β hp.ne' μ]
    simp_rw [parisiPhysicalOrderLaw_cdf β hp.ne' μ]
    have HE : (fun v : ℝ => v*α (v/β^2))=
        fun v => β^2*(α (v/β^2)*(v/β^2)) := by
      funext v
      field_simp
    rw [HE,intervalIntegral.integral_const_mul]
    field_simp
  have HI := intervalIntegral.integral_add_adjacent_intervals
    (parisiPhysicalOverlapPenalty_intervalIntegrable β μ 0 V)
    (parisiPhysicalOverlapPenalty_intervalIntegrable β μ V (β^2))
  have HT : (∫ v in V..β^2, α (v/β^2)*(v/β^2))=(β^2-(β^2)*Q^2)/2 := by
    have HE : (∫ v in V..β^2, α (v/β^2)*(v/β^2))=∫ v in V..β^2, v/β^2 := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      rw [uIcc_of_le hVb] at hv
      have H : α (v/β^2)=1 := by
        apply actualParisiEquilibrium_cdf_one_after_support β hβ
        apply (le_div_iff₀ (sq_pos_of_ne_zero hp.ne')).mpr
        simpa only [mul_comm] using hv.1
      rw [H,one_mul]
    rw [HE,intervalIntegral.integral_div,integral_id]
    dsimp [V]
    field_simp
  rw [HT] at HI
  rw [HF]
  change parisiPhysicalValue β μ 0 0-(1/2:ℝ)*(∫ v in 0..V, α (v/β^2)*(v/β^2))-
    (β^2-V)/2=_
  dsimp only [V]
  linarith [HI]

theorem parisiEquilibrium_entropy_energy_identity (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (ha : ∀ z, cdf (parisiEquilibriumMeasure β:Measure ℝ) z∈Icc (0:ℝ) 1)
    (h1 : cdf (parisiEquilibriumMeasure β:Measure ℝ) 1=1) :
    (∫ v in 0..(β^2*parisiEquilibriumSupportEndpoint β), parisiPreSusceptibilityExpected W β ha h1 v)+
      (∫ w, binarySpinEntropy (Real.tanh
        (finiteTemperatureCDFProcess W β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) ha h1
          (Real.toNNReal (β^2*parisiEquilibriumSupportEndpoint β)) w)) ∂W.law)=
      parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
        (β^2/4)*(1-parisiEquilibriumSupportEndpoint β)^2 := by
  rw [parisiEquilibrium_terminal_entropy_balance W β hβ ha h1,
    parisiEquilibrium_physical_pressure_cancellation β hβ]

end SKConstants
