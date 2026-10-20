module

public import SKBarriers2.Statement

@[expose] public section
noncomputable section
open scoped Topology
open Filter

namespace OAI.SK.Strengthened

/-- One positive coefficient, chosen before the threshold, at exponent `r`. -/
def MainStatementAt (r : ℝ) : Prop :=
  ∀ β : ℝ, 1 < β → ∃ A : ℝ, 0 < A ∧
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (continuousBadMass β A r τ) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β A r τ) atTop (𝓝 1)

/-- Unit coefficient at every positive exponent strictly below `r`. -/
def SubcriticalStatementBelow (r : ℝ) : Prop :=
  ∀ β κ : ℝ, 1 < β → 0 < κ → κ < r →
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (continuousBadMass β 1 κ τ) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β 1 κ τ) atTop (𝓝 1)

/-- The seven-thirtieths endpoint statement. -/
def MainStatementSevenThirty : Prop := MainStatementAt ((7 : ℝ) / 30)

/-- The subcritical corollary below seven thirtieths. -/
def SubcriticalStatementSevenThirty : Prop :=
  SubcriticalStatementBelow ((7 : ℝ) / 30)

end OAI.SK.Strengthened
