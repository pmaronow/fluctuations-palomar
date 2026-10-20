module

public import SKBarriers2.Corner.CoreIdentity

@[expose] public section

noncomputable section
open scoped Topology
open Filter Set OAI.SK.Analytic

namespace SKBarriers2

def CrudeC1 (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ N : ℕ, 1 ≤ N → ∀ z : ℝ,
        |cornerV β α r h k N z| ≤ C * h * k ^ 2 ∧
        |deriv (cornerV β α r h k N) z| ≤ C * h * k ^ 2

def CoreValue (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
        |cornerV β α r h k N z -
          (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
            h ^ 3 * cornerCubic β α (r - h) k z)| ≤
          C * (Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3) + ε

def CornerExpansion' (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ κ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧ 0 < κ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        OW.trialValue β α α r (h / 2) (h * k) N ≤ 3 * finiteParisiInf β +
          cornerMass β α (r - h) * h ^ 3 *
            SKOptimized.Overshoot.pressurePolynomial (1 / 2) k +
          C * (Real.sqrt h * h ^ 3 * k ^ 2 + h ^ 3 * |k| ^ 3) + ε

end SKBarriers2
