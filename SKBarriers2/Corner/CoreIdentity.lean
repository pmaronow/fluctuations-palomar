module

public import SKBarriers2.Interfaces

@[expose] public section

noncomputable section
open scoped Topology
open Filter Set OAI.SK.Analytic

namespace SKBarriers2

def cornerV (β : ℝ) (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ) : ℝ → ℝ :=
  fun z => OW.boundary β α (1 / 2) (r - h) h k N z -
    OW.boundary β α (1 / 2) (r - h) h 0 N z

def cornerPenalty (α : ℝ → ℝ) (r h k : ℝ) (N : ℕ) : ℝ :=
  matrixChainPenalty (OW.window α (1 / 2) (r - h) h k N) (fun _ _ => r - h) -
    matrixChainPenalty (OW.window α (1 / 2) (r - h) h 0 N) (fun _ _ => r - h)

def cornerQuadratic (β : ℝ) (α : ℝ → ℝ) (s z : ℝ) : ℝ :=
  β ^ 4 * jet β α 2 s z ^ 2 / 4

def cornerCubic (β : ℝ) (α : ℝ → ℝ) (s k z : ℝ) : ℝ :=
  α s ^ 2 * (β ^ 2) ^ 3 * jet β α 2 s z ^ 3 *
      (SKOptimized.Overshoot.riccatiJet (1 / 2) k -
        SKOptimized.Overshoot.riccatiJet (1 / 2) 0) +
    α s * (β ^ 2) ^ 3 * jet β α 3 s z ^ 2 *
      (SKOptimized.Overshoot.wickJet (1 / 2) k -
        SKOptimized.Overshoot.wickJet (1 / 2) 0)

def cornerMass (β : ℝ) (α : ℝ → ℝ) (s : ℝ) : ℝ :=
  α s ^ 2 * (β ^ 2) ^ 3 * scalarLaw β α s (fun z => jet β α 2 s z ^ 3)

def CoreIdentity (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ N : ℕ, 1 ≤ N → ∀ z : ℝ,
        |cornerV β α r h k N z -
          (cornerQuadratic β α (r - h) z * cornerPenalty α r h k N +
            h ^ 3 * cornerCubic β α (r - h) k z)| ≤
            C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2 ∧
        |deriv (cornerV β α r h k N) z -
          (deriv (cornerQuadratic β α (r - h)) z * cornerPenalty α r h k N +
            h ^ 3 * deriv (cornerCubic β α (r - h) k) z)| ≤
            C * (h ^ 4 + h ^ 2 / (N : ℝ)) * k ^ 2

def cornerNormPolynomial (k : ℝ) : ℝ := 16 / 9 * k ^ 2 - 248 / 243 * k ^ 4

def PenaltyBound (_β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ N : ℕ, 1 ≤ N → |cornerPenalty α r h k N| ≤ C * h ^ 2 * k ^ 2

def PenaltyExpansion (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ 1 / 2 →
      ∀ N : ℕ, 1 ≤ N →
        |cornerPenalty α r h k N - h ^ 2 * α (r - h) * cornerNormPolynomial k| ≤
          C * (h ^ 3 + h ^ 2 / (N : ℝ)) * k ^ 2

def CoreCoefficientControl (β : ℝ) (α : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
    |cornerQuadratic β α s z| ≤ B ∧
    |deriv (cornerQuadratic β α s) z| ≤ B ∧
    |cornerCubic β α s k z| ≤ B * k ^ 2 ∧
    |deriv (cornerCubic β α s k) z| ≤ B * k ^ 2

def cornerAverage (β : ℝ) (α : ℝ → ℝ) (r h : ℝ) (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  scalarCDFAverage β (fun t => α t / 3) 0 (Real.toNNReal (r - h))
    (OW.boundary β α (1 / 2) (r - h) h 0 N) g 0

def PrefixMomentConvergence (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ →
    (Tendsto (fun N => cornerAverage β α r h N (fun z => jet β α 2 (r - h) z ^ 2))
      atTop (𝓝 (scalarLaw β α (r - h) (fun z => jet β α 2 (r - h) z ^ 2)))) ∧
    (Tendsto (fun N => cornerAverage β α r h N (fun z => jet β α 2 (r - h) z ^ 3))
      atTop (𝓝 (scalarLaw β α (r - h) (fun z => jet β α 2 (r - h) z ^ 3)))) ∧
    (Tendsto (fun N => cornerAverage β α r h N (fun z => jet β α 3 (r - h) z ^ 2))
      atTop (𝓝 (scalarLaw β α (r - h) (fun z => jet β α 3 (r - h) z ^ 2))))

def UniformCornerMass (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ m₀ h₀ : ℝ, 0 < m₀ ∧ 0 < h₀ ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → m₀ ≤ cornerMass β α (r - h)

def CornerExpansion (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ : ℝ, 0 ≤ C ∧ 0 < h₀ ∧ ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ k : ℝ, |k| ≤ 1 / 2 →
      OW.trialValue β α α r (h / 2) (h * k) N ≤ 3 * finiteParisiInf β +
        cornerMass β α (r - h) * h ^ 3 * SKOptimized.Overshoot.pressurePolynomial (1 / 2) k +
        C * h ^ 4 * k ^ 2 + ε

end SKBarriers2
