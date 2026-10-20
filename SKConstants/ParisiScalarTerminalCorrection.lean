module
public import SKConstants.ParisiScalarEnergyEntropyIdentity
public import SKConstants.GrowingQueryMeshScales

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

lemma actualParisiFullSusceptibilityExpected_nonneg (W : BrownianSystem Ω) (β v : ℝ) :
    0≤actualParisiFullSusceptibilityExpected W β v :=
  integral_nonneg (fun w => (actualParisiFullMagnetization_curvature_bounds β v _).2.1)

theorem actualParisiContinuationP_square_le_exp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β)
    (S : ℝ) (hS : 1≤S) : (actualParisiContinuationP W β S)^2≤16*Real.exp (-S) := by
  have hS0 : 0<S := zero_lt_one.trans_le hS
  have HP := actualParisiContinuationP_le_tail W β S hS0
  have HP0 : 0≤actualParisiContinuationP W β S := by
    rw [←actualParisiFullSusceptibilityExpected_post W β hβ S hS0.le]
    exact actualParisiFullSusceptibilityExpected_nonneg W β _
  have hroot : 1≤Real.sqrt (2*Real.pi*S) := Real.one_le_sqrt.mpr (by
    have Hπ : 1≤Real.pi := by linarith [Real.pi_gt_three]
    nlinarith)
  have hi : (Real.sqrt (2*Real.pi*S))⁻¹≤1 := inv_le_one_of_one_le₀ hroot
  have HP1 : actualParisiContinuationP W β S≤4*Real.exp (-S/2) := by
    simp only [scalarTailScale,Real.coe_toNNReal S hS0.le,Nat.cast_ofNat] at HP
    exact HP.trans (by nlinarith [mul_le_mul_of_nonneg_left hi (Real.exp_pos (-S/2)).le])
  have HH := mul_self_le_mul_self HP0 HP1
  have HE : Real.exp (-S/2)*Real.exp (-S/2)=Real.exp (-S) := by
    rw [←Real.exp_add]
    congr 1
    ring
  nlinarith [HE]

theorem actualParisi_scalar_terminal_pressure_correction
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (S : ℝ) (hS : 1≤S) :
    0≤parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
      (Real.log 2-actualParisiEntropyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S)+
        β*actualParisiEnergyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S)) ∧
    parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
      (Real.log 2-actualParisiEntropyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S)+
        β*actualParisiEnergyReference W β ((parisiEquilibriumPhysicalEndpoint β:ℝ)+S))≤
          4*β^2*Real.exp (-S) := by
  rw [actualParisi_scalar_entropy_energy_identity_shifted W β hβ S (by linarith)]
  have H := mul_le_mul_of_nonneg_left (actualParisiContinuationP_square_le_exp W β hβ S hS)
    (show 0≤β^2/4 by positivity)
  constructor
  · nlinarith [sq_nonneg (actualParisiContinuationP W β S)]
  · nlinarith

theorem actualParisi_scalar_terminal_pressure_correction_log_horizon
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1<β) (F : ℝ) (n : ℕ) (hn : 0<n)
    (hF : 1≤F*Real.log (n:ℝ)) :
    parisiContinuumFunctional β (cdf (parisiEquilibriumMeasure β:Measure ℝ))-
      (Real.log 2-actualParisiEntropyReference W β
        ((parisiEquilibriumPhysicalEndpoint β:ℝ)+F*Real.log (n:ℝ))+
        β*actualParisiEnergyReference W β
          ((parisiEquilibriumPhysicalEndpoint β:ℝ)+F*Real.log (n:ℝ)))≤4*β^2*(n:ℝ)^(-F) := by
  have H := (actualParisi_scalar_terminal_pressure_correction W β hβ _ hF).2
  have HE : Real.exp (-(F*Real.log (n:ℝ)))=(n:ℝ)^(-F) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
    congr 1
    ring
  rwa [HE] at H

end SKConstants
