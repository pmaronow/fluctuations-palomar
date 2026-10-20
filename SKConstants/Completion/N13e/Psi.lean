module

public import SKConstants.Completion.N13e.ScalarBounds
public import SKConstants.Completion.LM4b.ActualPsi

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SKConstants.Completion.N13e
open SKConstantsOAI.ZeroTemperatureSK LM4b
variable {Ω : Type} [MeasurableSpace Ω]
variable {A : Type*} [MeasurableSpace A]

def coarsePsi (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (k : ℕ) (J : (Bool × Ω) × A → ℝ) : (Bool × Ω) × A → ℝ :=
  let t := growingQueryTime δ
  actualPsi W Z β hβ (t (k+1)) J t (actualCoarseWeight W β t)
    (actualCoarseNoiseWeight W β t) k (actualCoarseEnergy W β t k)

theorem coarsePsi_centered_moments
    (hprofile : Blueprint.SusceptibilityProfileStatement)
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks k : ℕ) (i : Fin (ranks+k))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks k
      (growingQueryTime δ (k+1)) i)
    (J : (Bool × Ω) × A → ℝ) (hJm : Measurable J)
    (hJ : IsActualRowDIntegral W Z β hβ (growingQueryTime δ (k+1)) J)
    (hsmall : ∀ j < k, (growingQueryDuration δ (j+1):ℝ) ≤ 1/8) :
    let V := growingQueryTime δ (k+1)
    let ν := actualParisiFullQuerySpinLaw W Z β V
    let X := Concentration.centeredObservable ν (coarsePsi W Z β hβ δ k J)
    (∀ p : ℕ, Integrable (fun u => X u^p) ν) ∧ (∫ u, X u ∂ν = 0) ∧
      (∀ p : ℕ, 2 ≤ p → (∫ u, |X u|^p ∂ν) ≤
        (p.factorial:ℝ) * (psiMomentConstant β * (1+(V:ℝ)))^p) := by
  obtain ⟨he, hv, hv0, hstart, herror, hbudget⟩ :=
    actualCoarsePsi_deterministic_inputs hprofile W β hβ δ hδ k hsmall
  exact actualPsi_centered_moments_of_primitives W Z β hβ δ hδ ranks k _ i htransport
    J hJm hJ (growingQueryTime δ) (growingQueryTime_strictMono δ hδ).monotone
    (actualCoarseWeight W β (growingQueryTime δ))
    (fun j => β*actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (j+1)))
    (actualCoarseNoiseWeight W β (growingQueryTime δ)) k
    (actualCoarseEnergy W β (growingQueryTime δ) k) he hv hv0 hstart herror hbudget

theorem coarsePsi_iid_abs
    (hprofile : Blueprint.SusceptibilityProfileStatement)
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks k : ℕ) (i : Fin (ranks+k))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks k
      (growingQueryTime δ (k+1)) i)
    (J : (Bool × Ω) × A → ℝ) (hJm : Measurable J)
    (hJ : IsActualRowDIntegral W Z β hβ (growingQueryTime δ (k+1)) J)
    (hsmall : ∀ j < k, (growingQueryDuration δ (j+1):ℝ) ≤ 1/8)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    let V := growingQueryTime δ (k+1)
    let ν := actualParisiFullQuerySpinLaw W Z β V
    (actualParisiFullMixedRowsLaw W Z β V n).real {u | (n:ℝ)*η ≤
      |∑ j : Fin n, Concentration.centeredObservable ν (coarsePsi W Z β hβ δ k J) (u j)|} ≤
      2 * Real.exp (-(n:ℝ) * min
        (η^2 / (8*(psiMomentConstant β*(1+(V:ℝ)))^2))
        (η / (4*(psiMomentConstant β*(1+(V:ℝ)))))) := by
  obtain ⟨he, hv, hv0, hstart, herror, hbudget⟩ :=
    actualCoarsePsi_deterministic_inputs hprofile W β hβ δ hδ k hsmall
  exact actualPsi_iid_abs_of_primitives W Z β hβ δ hδ ranks k _ i htransport J hJm hJ
    (growingQueryTime δ) (growingQueryTime_strictMono δ hδ).monotone
    (actualCoarseWeight W β (growingQueryTime δ))
    (fun j => β*actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (j+1)))
    (actualCoarseNoiseWeight W β (growingQueryTime δ)) k
    (actualCoarseEnergy W β (growingQueryTime δ) k) he hv hv0 hstart herror hbudget hn hη

theorem coarsePsi_integral_and_moments_exists
    (hprofile : Blueprint.SusceptibilityProfileStatement)
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks k : ℕ) (i : Fin (ranks+k))
    (htransport : ActualRowReferenceTransportStatement W Z β hβ δ hδ ranks k
      (growingQueryTime δ (k+1)) i)
    (hsmall : ∀ j < k, (growingQueryDuration δ (j+1):ℝ) ≤ 1/8) :
    ∃ J : (Bool × Ω) × A → ℝ, Measurable J ∧
      IsActualRowDIntegral W Z β hβ (growingQueryTime δ (k+1)) J ∧
      let V := growingQueryTime δ (k+1)
      let ν := actualParisiFullQuerySpinLaw W Z β V
      let X := Concentration.centeredObservable ν (coarsePsi W Z β hβ δ k J)
      (∀ p : ℕ, Integrable (fun u => X u^p) ν) ∧ (∫ u, X u ∂ν = 0) ∧
        (∀ p : ℕ, 2 ≤ p → (∫ u, |X u|^p ∂ν) ≤
          (p.factorial:ℝ) * (psiMomentConstant β * (1+(V:ℝ)))^p) := by
  obtain ⟨J, hJm, hJ⟩ := actualRowDIntegral_exists_of_transport W Z β hβ δ hδ ranks k _ i htransport
  exact ⟨J, hJm, hJ,
    coarsePsi_centered_moments hprofile W Z β hβ δ hδ ranks k i htransport J hJm hJ hsmall⟩

end SKConstants.Completion.N13e
