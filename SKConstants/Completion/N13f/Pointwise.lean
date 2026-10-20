module

public import SKConstants.Completion.N13f.InformationMean
public import SKConstants.Completion.N13f.Cost

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.N13f
open SKConstantsOAI.ZeroTemperatureSK Blueprint LM4b
variable {Ω : Type*} [MeasurableSpace Ω]

theorem coarse_pointwise_logLikelihood
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ)
    (hV : (parisiEquilibriumPhysicalEndpoint β : ℝ) ≤ growingQueryTime δ (k+1))
    (hsmall : ∀ i < k+1, growingQueryDuration δ i ≤ 1)
    (N I H ζ u R : ℝ) (hN : 0 < N)
    (hpsi : I/N-β*ζ ≤ actualParisiEntropyReference W β (growingQueryTime δ (k+1))-
      β*actualCoarseEnergy W β (growingQueryTime δ) k+u)
    (henergy : |H/N-ζ| ≤ u+R) :
    I-N*Real.log 2-β*H ≤ -N*parisiPressure β + N *
      (β^2/4*(actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (k+1)))^2 +
        β*(1/β^2+33*Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ)+1)/2))*(δ : ℝ) +
        (1+β)*u+β*R) := by
  have hβ0 : 0 ≤ β := by linarith
  have hq := actualCoarseEnergy_quadrature_error W β hβ δ hδ k hsmall
  have hquad := (abs_sub_comm (actualCoarseEnergy W β (growingQueryTime δ) k)
    (actualParisiEnergyReference W β (growingQueryTime δ (k+1)))).symm ▸ hq
  have hquad' := mul_le_mul_of_nonneg_left (le_abs_self
    (actualParisiEnergyReference W β (growingQueryTime δ (k+1))-
      actualCoarseEnergy W β (growingQueryTime δ) k)) hβ0
  have hquad'' := mul_le_mul_of_nonneg_left hquad hβ0
  have henergy' := mul_le_mul_of_nonneg_left (abs_le.mp henergy).1 hβ0
  have hbalance := actualParisi_scalar_entropy_energy_identity W β hβ _ hV
  change Real.log 2-_+β*_ = parisiPressure β-_ at hbalance
  have hstep : I/N-Real.log 2-β*(H/N) ≤ -parisiPressure β +
      (β^2/4*(actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (k+1)))^2 +
        β*(1/β^2+33*Real.exp (((parisiEquilibriumPhysicalEndpoint β : ℝ)+1)/2))*(δ : ℝ) +
        (1+β)*u+β*R) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hstep hN.le
  convert hm using 1 <;> field_simp

end SKConstants.Completion.N13f
