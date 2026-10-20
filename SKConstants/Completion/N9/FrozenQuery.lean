module

public import SKConstants.Completion.N9.QueryBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine
variable {Ω : Type*} [MeasurableSpace Ω]

def frozenQueryTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a : ℝ≥0) {n : ℕ} (s : ℝ) (m₀ : Fin n → ℝ)
    (Bpast Dpast : Fin n → ScalarContinuousPath a) : Fin n → ℝ :=
  fun i => (fixedPastPosterior W β hβ a (Bpast i) (Dpast i)-m₀ i)/s

def frozenQueryMixedMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) {n : ℕ} (Bpast Dpast : Fin n → ScalarContinuousPath a) : Fin n → ℝ :=
  mixedMean (freshRowsLaw W h f n)
    (gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j)))

def frozenQueryExpectation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) {n m : ℕ} (s : ℝ)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (m₀ : Fin n → ℝ)
    (Bpast Dpast : Fin n → ScalarContinuousPath a) : ℝ :=
  let t := frozenQueryTarget W β hβ a s m₀ Bpast Dpast
  let row := gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))
  ∫ z, oneQueryEnergy row n (normalizedQuery n (paperFrame E t 0))
    (remainingProjection (paperFrame E t)) z ∂freshRowsLaw W h f n

end SKConstants.Completion.N9
