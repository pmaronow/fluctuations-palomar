module

public import SKConstants.Completion.N9b.ThresholdMean
public import SKConstants.Completion.N9b.SourceMoments
public import SKConstants.Completion.N9b.EnergyBridge

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 LQ
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem fineEnergy_frozenQuery_regular_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (a h f : ℝ≥0)
    (n m j : ℕ) (hn : 0 < n) (hdim : m+j=n)
    (s d L M b : ℝ) (hs : 0 < s) (hd : 0 ≤ d) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (E : Ξ → Matrix (Fin (m+1)) (Fin n) ℝ) (m₀ : Ξ → Fin n → ℝ)
    (B D : Ξ → Fin n → ScalarContinuousPath a)
    (hE : ∀ p i k, dot (E p i) (E p k) = if i=k then 1 else 0)
    (hm₀ : ∀ p, E p *ᵥ m₀ p = 0)
    (hEm : Measurable E) (hm₀m : Measurable m₀) (hB : Measurable B) (hD : Measurable D)
    (hposterior : ∀ p, FreshPosteriorMeanStatement W β hβ a h f n (B p) (D p)) :
    let T := fun p => frozenQueryTarget W β hβ a s (m₀ p) (B p) (D p)
    let ζ := fun p => frozenQueryMixedMean W β hβ a h f (B p) (D p)
    let Y := fun p => queryRemovedSquare n (E p) (T p)
    let z := fun p => (n : ℝ)⁻¹*∑ i, ζ p i
    (∀ p i, 0 ≤ ζ p i ∧ ζ p i ≤ L*s) →
    (∀ i, Measurable (fun p => (ζ p i,T p i))) →
    iIndepFun (fun i p => (ζ p i,T p i)) μ →
    (∀ i, MemLp (fun p => T p i) 4 μ) →
    (∀ i, (∫ p, T p i^2 ∂μ) = 1) →
    (∀ i, (∫ p, T p i^4 ∂μ) ≤ M*d/s^2) →
    (∫ p, z p ∂μ) = b →
    Integrable Y μ → Integrable (fun p => Y p^2) μ →
    (∫ p, Y p ∂μ) ≤ (j : ℝ)*d/((n : ℝ)*s^2) →
    (∫ p, Y p^2 ∂μ) ≤ 3*((j : ℝ)^2+j)*d^2/((n : ℝ)^2*s^4) →
    s*b-((M+4)*L)*fineCellError n j s d ≤
      ∫ p, frozenQueryExpectation W β hβ a h f s (E p) (m₀ p) (B p) (D p) ∂μ := by
  dsimp only
  intro hζ hm hind hT hunit hfour hmean hY hY2 hEY hEY2
  exact fineEnergy_frozenQuery_holds W β hβ μ a h f n m j hn hdim s d L M b
    hs hd hL hM E m₀ B D hE hm₀ hposterior hζ hm hind hT hunit hfour hmean hY hY2 hEY hEY2
    (frozenQueryExpectation_integrable W β hβ μ a h f n m s E m₀ B D hE hEm hm₀m hB hD)

theorem fineEnergyBudget_ge_mesh (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K : ℕ) (N : ℝ) (hN : 0 < N) :
    (δ : ℝ) ≤ fineEnergyBudget W β δ K N := by
  have hr := actual_square_profile_pos W β hβ (scalarGrowingSourceHorizon δ K)
    (scalarGrowingSourceHorizon δ K).coe_nonneg
  unfold fineEnergyBudget
  calc
    _ ≤ (δ : ℝ)+(((K : ℝ)+1)*(1+(scalarGrowingSourceHorizon δ K : ℝ))+Real.sqrt K)/N :=
      le_add_of_nonneg_right (by positivity)
    _ ≤ _ := le_add_of_nonneg_right (by positivity)

end SKConstants.Completion.N9b

namespace SKConstants.Completion.N9b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LFine N9
variable {Ω : Type} [MeasurableSpace Ω]

theorem fineEnergy_zeroQueries_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ≥0), 0 < δ → ∀ r : ℕ, 0 < r →
      (growingQueryDuration δ 0 : ℝ) ≤ 1/8 →
      actualParisiEnergyReference W β (scalarGrowingSourceHorizon δ 0) -
        C*fineEnergyBudget W β δ 0 (r+0 : ℕ) ≤
      (∫ y, goeSpinHamiltonian (1/Real.sqrt (2*(r+0 : ℕ))) y.1 y.2
        ∂replayProposalGen W β hβ δ r 0 rfl)/(r+0 : ℕ) := by
  refine ⟨fineEnergyQuadratureConstant β, fineEnergyQuadratureConstant_nonneg β, ?_⟩
  intro δ hδ r hr hsmall
  have hd : (δ : ℝ) ≤ 1 := by
    have h0 : (growingQueryDuration δ 0 : ℝ) = (δ : ℝ) := by
      simp only [growingQueryDuration_coe, growingQueryTime_zero, NNReal.coe_zero,
        zero_div, Real.exp_zero, mul_one]
    rw [h0] at hsmall
    linarith
  have hbase := fineEnergy_source_zeroQueries_holds W β hβ δ hδ hd r hr
  have hbudget := fineEnergyBudget_ge_mesh W β hβ δ 0 (r+0 : ℕ) (by exact_mod_cast hr)
  rw [replayProposalGen_energy_eq_source W β hβ δ r 0 (by omega)]
  nlinarith [mul_le_mul_of_nonneg_left hbudget (fineEnergyQuadratureConstant_nonneg β)]

end SKConstants.Completion.N9b
