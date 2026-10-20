module

public import SKConstants.Completion.NL1.Coefficients
public import SKConstants.Completion.NL1.Primitive
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5 LGram N13A LM5

variable {Ω : Type} [MeasurableSpace Ω]

theorem rowGramEvent_cast {m n d : ℕ} (h : m = n)
    (P : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (z : Fin m → EuclideanSpace ℝ (Fin d)) :
    (fun i : Fin n => z (Fin.cast h.symm i)) ∈ rowGramEvent P n ε ↔
      z ∈ rowGramEvent P m ε := by
  subst n
  rfl

theorem sourceSharpRows_gramGood_iff (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ)
    (u : (Fin (coarseRank p n + coarseCount p n) → Bool) ×
      M1.SourceInput (coarseMesh p n) (coarseRank p n) (coarseCount p n)) :
    sourceSharpRows W β hβ p n u ∈ gramGood W β hβ p n ↔
      u ∈ sourceWholeGramEvent W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (1 / (16 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2)) :=
  rowGramEvent_cast (rankCount_add p.a p.b n) _ _ _

theorem arrayCoefficients_reindex {p : Parameters} {n m : ℕ} (h : m = n)
    (z : Fin m → EuclideanSpace ℝ (Fin (coarseCount p n + (coarseCount p n + 1)))) :
    arrayCoefficients (p := p) (n := n) (fun i => z (Fin.cast h.symm i)) =
      familyCoordinates (gramSchmidtNormed ℝ (fun j => (Real.sqrt (n : ℝ))⁻¹ •
        WithLp.toLp 2 (fun i => z i (posteriorIndex _ j))))
        ((Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 (fun i => z i (spinIndex _))) := by
  subst n
  rfl

theorem arrayCoefficients_sourceSharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n)
    (u : (Fin (coarseRank p n + coarseCount p n) → Bool) ×
      M1.SourceInput (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (hu : sourceSharpRows W β hβ p n u ∈ gramGood W β hβ p n) :
    arrayCoefficients (sourceSharpRows W β hβ p n u) =
      N13d.growingCoefficients W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (growingSourceCompact (coarseMesh p n) (coarseRank p n) (coarseCount p n) u).1 := by
  have hδ := paperGrowingQueryMeshSize_pos p.a n hn
  have hN : 0 < coarseRank p n + coarseCount p n := by
    simpa only [coarseRank, coarseCount, rankCount_add] using hn
  have hblocks := actualSource_good_blocks W β hβ _ hδ _ _ _ u
    ((sourceSharpRows_gramGood_iff W β hβ p n u).mp hu)
  have hGram := hblocks.1.trans (gramTolerance_le_three_quarters (coarseCount p n))
  unfold sourceSharpRows
  rw [arrayCoefficients_reindex (rankCount_add p.a p.b n)]
  have hcast : (n : ℝ) = ((coarseRank p n + coarseCount p n : ℕ) : ℝ) :=
    (congrArg (fun N : ℕ => (N : ℝ)) (rankCount_add p.a p.b n)).symm
  rw [hcast]
  simp only [literalSourceRows, paperRows, posteriorIndex, spinIndex,
    Fin.append_left, Fin.append_right]
  rw [N13d.growingCoefficients_eq_source, N13d.paperSpinCoefficients_eq_coordinates _ _ _
    (Nat.cast_pos.mpr hN)]
  congr 1
  funext j
  exact (actualPaper_directionTrace_eq_gramSchmidtNormed _ _ _ _ _ _
    (Real.sqrt ((coarseRank p n + coarseCount p n : ℕ) : ℝ))⁻¹
    (by positivity) hGram j).symm

theorem completionVariance_eq_discardedVariance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n)
    (u : (Fin (coarseRank p n + coarseCount p n) → Bool) ×
      M1.SourceInput (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (hu : sourceSharpRows W β hβ p n u ∈ gramGood W β hβ p n) :
    completionVariance (coarseRank p n + coarseCount p n : ℕ)
      (fun j => N13d.growingCoefficients W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (growingSourceCompact (coarseMesh p n) (coarseRank p n) (coarseCount p n) u).1 j)
      (N13d.growingResidual W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (growingSourceCompact (coarseMesh p n) (coarseRank p n) (coarseCount p n) u).1) =
      discardedVariance (sourceSharpRows W β hβ p n u) := by
  have hN : 0 < coarseRank p n + coarseCount p n := by
    simpa only [coarseRank, coarseCount, rankCount_add] using hn
  unfold completionVariance discardedVariance
  rw [N13d.growingResidual_norm_identity W β hβ _ _ _ hN,
    ← arrayCoefficients_sourceSharpRows W β hβ p n hn u hu,
    ← EuclideanSpace.real_norm_sq_eq]
  have hcast : ((coarseRank p n + coarseCount p n : ℕ) : ℝ) = (n : ℝ) :=
    congrArg (fun N : ℕ => (N : ℝ)) (rankCount_add p.a p.b n)
  rw [hcast]
  ring

end SKConstants.Completion.NL1
