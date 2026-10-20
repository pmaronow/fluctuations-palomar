module

public import SKConstants.Completion.LJ.FiniteRow
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def residualCoarseA (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (K j : ℕ) : ℝ :=
  if j < K then gridQueryMean W β t j / gridPosteriorScale W β t j else 0

def residualCoarseB (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (j : ℕ) : ℝ :=
  if j = 0 then 0 else gridPosteriorScale W β t (j - 1) /
    Real.sqrt ((t (j + 1) : ℝ) - t j)

def coarseCellRow (t : ℕ → ℝ≥0) (a b : ℕ → ℝ) (K : ℕ)
    (m B : ℝ≥0 → ℝ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (K + 1), a j * (rowPotential x (m (t (j + 1))) - rowPotential x (m (t j)))) +
    ∑ j ∈ Finset.range (K + 1), b j * (x - m (t j)) * (B (t (j + 1)) - B (t j))

theorem actualFiniteRow_raw_eq_coarse (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (K : ℕ) (u : (Bool × Ω) × A) :
    actualFiniteRow W Z β hβ t K u + gridEnergy W β t K / 2 =
      coarseCellRow t (residualCoarseA W β t K) (residualCoarseB W β t) K
        (fun v => actualParisiFullPosteriorMean W β v u.1.2)
        (fun v => (actualParisiQueryBrownianSystem W Z β hβ).B v (u.1.2, u.2))
        (scalarHiddenSign u.1.1) := by
  unfold actualFiniteRow coarseCellRow
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [residualCoarseA, lt_self_iff_false, ↓reduceIte, zero_mul,
    residualCoarseB, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, Nat.add_sub_cancel,
    add_zero, zero_add]
  simp only [sub_add_cancel, actualRowPotential]
  congr 1
  · rw [Fin.sum_univ_eq_sum_range (fun j => gridQueryMean W β t j / gridPosteriorScale W β t j *
      (rowPotential (scalarHiddenSign u.1.1) (actualParisiFullPosteriorMean W β (t (j + 1)) u.1.2) -
        rowPotential (scalarHiddenSign u.1.1) (actualParisiFullPosteriorMean W β (t j) u.1.2)))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ite_eq_left (Finset.mem_range.mp hj)]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => gridPosteriorScale W β t j /
      Real.sqrt ((t (j + 1 + 1) : ℝ) - t (j + 1)) *
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t (j + 1)) u.1.2) *
        ((actualParisiQueryBrownianSystem W Z β hβ).B (t (j + 1 + 1)) (u.1.2, u.2) -
          (actualParisiQueryBrownianSystem W Z β hβ).B (t (j + 1)) (u.1.2, u.2)))]
    apply Finset.sum_congr rfl
    intro j _
    simp only [gridQuery, scalarNormalizedBrownianRow]
    ring

def refinedContinuumRow (β : ℝ) (p q : ℝ≥0 → ℝ) (f : ℕ → ℕ → ℝ≥0)
    (K N : ℕ) (m B : ℝ≥0 → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range N,
    (β * p (f j i) * (rowPotential x (m (f j (i + 1))) - rowPotential x (m (f j i))) +
      q (f j i) * (x - m (f j i)) * (B (f j (i + 1)) - B (f j i)))

def refinedResidualLinear (β : ℝ) (p q : ℝ≥0 → ℝ) (a b : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ≥0) (K N : ℕ) (m B : ℝ≥0 → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range N,
    ((β * p (f j i) - a j) * (m (f j (i + 1)) - m (f j i)) +
      (q (f j i) - b j) * (B (f j (i + 1)) - B (f j i)))

def refinedResidualPredictable (β : ℝ) (p q : ℝ≥0 → ℝ) (a b : ℕ → ℝ)
    (t : ℕ → ℝ≥0) (f : ℕ → ℕ → ℝ≥0) (K N : ℕ) (m B : ℝ≥0 → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range N,
    (-(β * p (f j i) - a j) * m (f j i) * (m (f j (i + 1)) - m (f j i)) -
      (q (f j i) - b j) * m (t j) * (B (f j (i + 1)) - B (f j i)))

def refinedResidualQuadratic (β : ℝ) (p : ℝ≥0 → ℝ) (a : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ≥0) (K N : ℕ) (m : ℝ≥0 → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range N,
    -(β * p (f j i) - a j) * (m (f j (i + 1)) - m (f j i)) ^ 2 / 2

def refinedResidualLag (q : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (f : ℕ → ℕ → ℝ≥0)
    (K N : ℕ) (m B : ℝ≥0 → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range N,
    q (f j i) * (m (f j i) - m (t j)) * (B (f j (i + 1)) - B (f j i))

theorem refinedResidual_decomposition (β : ℝ) (p q : ℝ≥0 → ℝ) (a b : ℕ → ℝ)
    (t : ℕ → ℝ≥0) (f : ℕ → ℕ → ℝ≥0) (K N : ℕ)
    (hf0 : ∀ j < K + 1, f j 0 = t j) (hfN : ∀ j < K + 1, f j N = t (j + 1))
    (m B : ℝ≥0 → ℝ) (x : ℝ) :
    refinedContinuumRow β p q f K N m B x - coarseCellRow t a b K m B x =
      x * refinedResidualLinear β p q a b f K N m B +
        refinedResidualPredictable β p q a b t f K N m B +
        refinedResidualQuadratic β p a f K N m - refinedResidualLag q t f K N m B := by
  have hA (j : ℕ) (hj : j < K + 1) :
      (∑ i ∈ Finset.range N, a j *
        (rowPotential x (m (f j (i + 1))) - rowPotential x (m (f j i)))) =
        a j * (rowPotential x (m (t (j + 1))) - rowPotential x (m (t j))) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => rowPotential x (m (f j i))) N,
      hf0 j hj, hfN j hj]
  have hB (j : ℕ) (hj : j < K + 1) :
      (∑ i ∈ Finset.range N, b j * (x - m (t j)) * (B (f j (i + 1)) - B (f j i))) =
        b j * (x - m (t j)) * (B (t (j + 1)) - B (t j)) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => B (f j i)) N, hf0 j hj, hfN j hj]
  have hc : coarseCellRow t a b K m B x =
      ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range N,
        (a j * (rowPotential x (m (f j (i + 1))) - rowPotential x (m (f j i))) +
          b j * (x - m (t j)) * (B (f j (i + 1)) - B (f j i))) := by
    simp_rw [Finset.sum_add_distrib]
    unfold coarseCellRow
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj
    · exact (hA j (Finset.mem_range.mp hj)).symm
    · exact (hB j (Finset.mem_range.mp hj)).symm
  rw [hc]
  unfold refinedContinuumRow refinedResidualLinear refinedResidualPredictable
    refinedResidualQuadratic refinedResidualLag
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold rowPotential
  ring

def actualRefinedResidual (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (f : ℕ → ℕ → ℝ≥0) (K N : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  refinedContinuumRow β (fun v => actualParisiFullSusceptibilityExpected W β v)
    (fun v => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v)) f K N
    (fun v => actualParisiFullPosteriorMean W β v u.1.2)
    (fun v => (actualParisiQueryBrownianSystem W Z β hβ).B v (u.1.2, u.2))
    (scalarHiddenSign u.1.1) - (actualFiniteRow W Z β hβ t K u + gridEnergy W β t K / 2)

theorem actualRefinedResidual_decomposition (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (f : ℕ → ℕ → ℝ≥0) (K N : ℕ)
    (hf0 : ∀ j < K + 1, f j 0 = t j) (hfN : ∀ j < K + 1, f j N = t (j + 1))
    (u : (Bool × Ω) × A) :
    let p := fun v : ℝ≥0 => actualParisiFullSusceptibilityExpected W β v
    let q := fun v : ℝ≥0 => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v)
    let a := residualCoarseA W β t K
    let b := residualCoarseB W β t
    let m := fun v => actualParisiFullPosteriorMean W β v u.1.2
    let B := fun v => (actualParisiQueryBrownianSystem W Z β hβ).B v (u.1.2, u.2)
    actualRefinedResidual W Z β hβ t f K N u =
      scalarHiddenSign u.1.1 * refinedResidualLinear β p q a b f K N m B +
        refinedResidualPredictable β p q a b t f K N m B +
        refinedResidualQuadratic β p a f K N m - refinedResidualLag q t f K N m B := by
  dsimp only
  unfold actualRefinedResidual
  rw [actualFiniteRow_raw_eq_coarse]
  exact refinedResidual_decomposition β _ _ _ _ t f K N hf0 hfN _ _ _

end SKConstants.Completion.LJ
