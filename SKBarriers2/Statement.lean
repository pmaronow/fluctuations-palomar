module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import OAI.Probability.SKBarriers.Model

@[expose] public section

/-! Frozen target statements for the strengthened SK barrier
(manuscript `research/sk-barriers/manuscript/StrengthenedSKBarriers.tex`, Theorem `thm:main`
and Corollary `cor:subcritical`).

The model, disorder law, Gibbs weights, heat-bath kernels and total-variation distances are
the upstream `OAI.SK` definitions (openai/math `fd4aeeb`). Only the horizon and threshold are
parameters. Specializing to `A = 1`, `κ = OAI.SK.kappa`, `τ = 1/4` recovers the upstream bad
masses. -/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter

namespace OAI.SK.Strengthened

/-- Horizon `exp (A n^κ)`. -/
def timeScale (A κ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (A * (n : ℝ) ^ κ)

/-- Disorder-averaged Gibbs mass of starting states whose continuous-time distance to
equilibrium at the horizon exceeds `τ`. -/
def continuousBadMass (β A κ τ : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n,
    if τ < continuousDistance β J x (timeScale A κ n)
    then gibbs β J x else 0) ∂disorderLaw n

/-- The discrete-time analogue, at `⌊horizon⌋` heat-bath attempts. -/
def discreteBadMass (β A κ τ : ℝ) (n : ℕ) : ℝ :=
  ∫ J : Disorder n, (∑ x : Config n,
    if τ < discreteDistance β J x ⌊timeScale A κ n⌋₊
    then gibbs β J x else 0) ∂disorderLaw n

/-- **Theorem `thm:main`.** One coefficient `A > 0`, chosen before the threshold, works for
every fixed `τ ∈ (0, 1/2)` at horizon `exp (A n^{2/9})`. -/
def MainStatement : Prop :=
  ∀ β : ℝ, 1 < β → ∃ A : ℝ, 0 < A ∧
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (continuousBadMass β A ((2 : ℝ) / 9) τ) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β A ((2 : ℝ) / 9) τ) atTop (𝓝 1)

/-- **Corollary `cor:subcritical`.** Unit coefficient at every exponent `0 < κ < 2/9`. -/
def SubcriticalStatement : Prop :=
  ∀ β κ : ℝ, 1 < β → 0 < κ → κ < (2 : ℝ) / 9 →
    ∀ τ : ℝ, 0 < τ → τ < (1 / 2 : ℝ) →
      Tendsto (continuousBadMass β 1 κ τ) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β 1 κ τ) atTop (𝓝 1)

/-- Sanity link to upstream: the parameterized bad masses specialize to `OAI.SK`'s. -/
theorem continuousBadMass_upstream (β : ℝ) :
    continuousBadMass β 1 OAI.SK.kappa (1 / 4) = OAI.SK.continuousBadMass β := by
  funext n; simp [continuousBadMass, OAI.SK.continuousBadMass, timeScale, OAI.SK.timeScale]

theorem discreteBadMass_upstream (β : ℝ) :
    discreteBadMass β 1 OAI.SK.kappa (1 / 4) = OAI.SK.discreteBadMass β := by
  funext n; simp [discreteBadMass, OAI.SK.discreteBadMass, timeScale, OAI.SK.timeScale]

end OAI.SK.Strengthened
