module

public import SKConstants.Completion.LGram.All
public import SKConstants.Completion.LGram.SourceMeasurable

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13bc
open SKConstantsOAI.ZeroTemperatureSK LGram

def fixedGramTolerance (r : ℕ) : ℝ := (16 * (r + 1 : ℝ)^2)⁻¹

theorem fixedGramTolerance_pos (r : ℕ) : 0 < fixedGramTolerance r := by
  unfold fixedGramTolerance
  positivity

theorem fixedGramTolerance_le_one (r : ℕ) : fixedGramTolerance r ≤ 1 := by
  have hr : (1 : ℝ) ≤ r + 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  unfold fixedGramTolerance
  exact inv_le_one_of_one_le₀ (by nlinarith)

theorem fixedGramTolerance_small (r : ℕ) :
    16 * (r + 1 : ℝ)^2 * fixedGramTolerance r = 1 := by
  unfold fixedGramTolerance
  exact mul_inv_cancel₀ (by positivity)

theorem gramTailBudget_fixed (N d r : ℕ) (R : ℝ) :
    gramTailBudget N d R (fixedGramTolerance r) =
      2 * Real.exp ((d : ℝ) * Real.log 9 -
        (N : ℝ) / (196608 * (r + 1 : ℝ)^4 * Concentration.squareVarianceScale R 3)) := by
  rw [gramTailBudget_eq_exponential N d R _
    (fixedGramTolerance_pos r).le (fixedGramTolerance_le_one r)]
  congr 2
  congr 1
  unfold fixedGramTolerance
  simp only [div_eq_mul_inv, mul_inv_rev, mul_pow, inv_pow]
  norm_num
  ring

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem growingMixedRows_fixedGram_compl_le
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K N r : ℕ) (hN : 0 < N) :
    (mixedVectorRowsLaw W Z β hβ (growingQueryTime δ)
      (fun j => growingQueryTime δ (j+1)) K (growingQueryTime δ (K+1)) N).real
      (rowGramEvent (mixedPopulation W Z β hβ (growingQueryTime δ)
        (fun j => growingQueryTime δ (j+1)) K (growingQueryTime δ (K+1))) N
        (fixedGramTolerance r))ᶜ ≤
      2 * Real.exp ((K + (K+1) : ℕ) * Real.log 9 - (N : ℝ) /
        (196608 * (r+1 : ℝ)^4 * Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ K)) 3)) := by
  simpa only [gramTailBudget_fixed] using
    growingMixedRows_wholeGram_compl_le W Z β hβ δ hδ K hN
      (fixedGramTolerance r) (fixedGramTolerance_pos r)

theorem actualSource_fixedGram_compl_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (n₀ K r : ℕ) (hN : 0 < n₀+K)
    (hrow : SourceMixedRowsLawStatement W β hβ δ n₀ K) :
    (M1.SourceLinkedLaw W β hβ δ n₀ K).real
      (sourceWholeGramEvent W β hβ δ n₀ K (fixedGramTolerance r))ᶜ ≤
      2 * Real.exp ((K + (K+1) : ℕ) * Real.log 9 - (n₀+K : ℕ) /
        (196608 * (r+1 : ℝ)^4 * Concentration.squareVarianceScale
          (actualParisiFullMixedRowMGFProxy W β (growingQueryTime δ K)) 3)) := by
  simpa only [gramTailBudget_fixed] using
    actualSource_wholeGram_compl_le W β hβ δ hδ n₀ K hN
      (fixedGramTolerance r) (fixedGramTolerance_pos r) hrow

end SKConstants.Completion.N13bc
