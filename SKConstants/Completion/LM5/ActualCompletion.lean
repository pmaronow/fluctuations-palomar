module

public import SKConstants.Completion.LM5.NoiseRegrouping
public import SKConstants.Completion.LM5.ProjectionBudget
public import SKConstants.GaussianProposalTraceSteps
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix RealInnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5

variable {Past : Type*}

theorem actualPaper_energy_eq_query_add_completion (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) :
    quadraticEnergy N x (paperTensorProposal r (r+K) (skSigma N) target update K (a,1) z) =
      paperQueryEnergy r (r+K) N target update K (a,1) z x +
      completionEnergy N (paperSpinCoefficients r K N target update a z x)
        (paperResidualSpin r K target update a z x)
        (compactUnused (r+K) K (sourceSplit (r+K) K z).2) := by
  rw [paperTensorProposal_energy r (r+K) N hN]
  change paperQueryEnergy r (r+K) N target update K (a,1) z x + _ + _ = _ + (_ + _)
  rw [add_assoc]
  congr 1
  have hsym : (paperResidualProjection r (r+K) target update K (a,1) z).IsSymm :=
    paperRemainingProjectionTrace_symm r (r+K) target update K (a,1) z (Fin.last K)
  rw [quadraticEnergy_projected N x
    (paperResidualProjection r (r+K) target update K (a,1) z) _ hsym,
    compactUnused_source_residual]
  congr 1
  · simp only [discardedDiagonalEnergy, linearForm, paperSpinCoefficients,
      paperDiagonalTrace, compactUnused_source_diagonal]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem proposalTerminalPast_factors_visible (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K) :
    proposalTerminalPast update K s.1 z =
      proposalTerminalPast update K s.1 (visibleSource n K (sourceSplit n K z).1) := by
  have h := congrFun (paperScalarPastTrace_factors_visible r n target update hblind K s z)
    (Fin.last K)
  simpa only [paperScalarPastTrace_last] using h

theorem paperSpinCoefficients_factors_visible (r K : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) :
    paperSpinCoefficients r K N target update a z x =
      paperSpinCoefficients r K N target update a
        (visibleSource (r+K) K (sourceSplit (r+K) K z).1) x := by
  have h := paperQueryDirectionTrace_eq_of_visible_eq r (r+K) N target update hblind K
    (a,1) z (visibleSource (r+K) K (sourceSplit (r+K) K z).1)
    (by rw [sourceSplit_visibleSource])
  unfold paperSpinCoefficients
  rw [h]

theorem paperResidualSpin_factors_visible (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (x : Fin (r+K) → ℝ) :
    paperResidualSpin r K target update a z x =
      paperResidualSpin r K target update a
        (visibleSource (r+K) K (sourceSplit (r+K) K z).1) x := by
  have h := paperRemainingProjectionTrace_eq_of_visible_eq r (r+K) target update hblind K
    (a,1) z (visibleSource (r+K) K (sourceSplit (r+K) K z).1)
    (by rw [sourceSplit_visibleSource])
  unfold paperResidualSpin paperResidualProjection
  rw [h]

theorem actualPaper_sign_completion_law (r K : ℕ) (hN : 0 < r+K)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (v : PaperCompletionNoise (r+K) K) (x : Fin (r+K) → Bool) :
    let z := visibleSource (r+K) K v
    let c := paperSpinCoefficients r K (r+K : ℕ) target update a z (signSpin x)
    let y := paperResidualSpin r K target update a z (signSpin x)
    HasLaw (completionEnergy (r+K : ℕ) c y)
      (gaussianReal 0 (completionVariance (r+K : ℕ) c y).toNNReal)
      (completionNoiseLaw (r+K) K) ∧
      completionVariance (r+K : ℕ) c y ≤ (1/2 : ℝ) * ((r+K : ℕ) : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  exact ⟨completion_law _ hp _ _, actualPaper_sign_completionVariance_le r K hN target update a _ x⟩

theorem actualPaper_sign_completion_tail (r K : ℕ) (hN : 0 < r+K)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (v : PaperCompletionNoise (r+K) K) (x : Fin (r+K) → Bool)
    (u : ℝ) (hu : 0 < u) :
    let z := visibleSource (r+K) K v
    (completionNoiseLaw (r+K) K).real {w | u ≤ |completionEnergy (r+K : ℕ)
      (paperSpinCoefficients r K (r+K : ℕ) target update a z (signSpin x))
      (paperResidualSpin r K target update a z (signSpin x)) w|} ≤
      2 * Real.exp (-((r+K : ℕ) : ℝ)*u^2) := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  exact completion_tail _ hp _ _
    (actualPaper_coefficient_budget r K _ hp target update a _ _ (signSpin_norm_sq x))
    (actualPaper_residual_norm_identity r K _ hp target update a _ _ (signSpin_norm_sq x)) u hu

end SKConstants.Completion.LM5
