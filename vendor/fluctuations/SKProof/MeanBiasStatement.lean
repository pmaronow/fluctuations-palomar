module

public import SKFluctuationsOAI.Probability.SKFluctuations.Spin

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators Topology

namespace OAI.SKFluctuations.MeanBias

/-- The logarithm of the counting-measure partition function, without completion. -/
def countingLogPartition (β : ℝ) (n : ℕ) (g : Disorder n) : ℝ :=
  Real.log (∑ σ : Spin n, Real.exp (hamiltonian β n g σ))

/-- The expected counting-measure log partition function per spin. -/
def countingPressure (β : ℝ) (n : ℕ) : ℝ :=
  (∫ g, countingLogPartition β n g ∂disorderLaw n) / (n : ℝ)

/-- The thermodynamic pressure, defined from the actual finite-volume pressures. -/
def limitingPressure (β : ℝ) : ℝ :=
  limUnder atTop (countingPressure β)

/-- Corollary C: every positive exponent slack in the lower mean-bias bound. -/
def LowerBoundStatement : Prop :=
  ∀ β : ℝ, 1 < β → ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      c * (n : ℝ) ^ (-(5 / 6 : ℝ) - ε) ≤
        limitingPressure β - countingPressure β n

end OAI.SKFluctuations.MeanBias
