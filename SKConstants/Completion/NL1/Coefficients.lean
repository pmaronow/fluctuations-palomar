module

public import SKConstants.Completion.NL1.Energy
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal Topology

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint Blueprint4 LC5 LGram N13A LM5

variable {Ω : Type} [MeasurableSpace Ω]

theorem norm_toLp_le_one_of_sum_sq_le {k : ℕ} (c : Fin k → ℝ)
    (hc : (∑ j, (c j)^2) ≤ 1) : ‖WithLp.toLp 2 c‖ ≤ 1 := by
  have h : ‖WithLp.toLp 2 c‖^2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hc
  nlinarith

theorem gramSchmidt_coordinates_cast {m n k : ℕ} (h : m = n)
    (T : Fin k → Fin m → ℝ) (x : Fin n → ℝ) (s : ℝ) :
    familyCoordinates (gramSchmidtNormed ℝ (fun j => s • WithLp.toLp 2
      (fun i : Fin n => T j (Fin.cast h.symm i)))) (s • WithLp.toLp 2 x) =
    familyCoordinates (gramSchmidtNormed ℝ (fun j => s • WithLp.toLp 2 (T j)))
      (s • WithLp.toLp 2 (fun i => x (Fin.cast h i))) := by
  subst n
  rfl

theorem arrayCoefficients_eq_replay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    arrayCoefficients (sharpRows W β hβ p n y) =
      familyCoordinates (gramSchmidtNormed ℝ (replayTargetFamily W β hβ p n y))
        (replaySpinVector p n y) := by
  unfold arrayCoefficients
  have hx : arrayX (sharpRows W β hβ p n y) = fun i => scalarHiddenSign (y.1 i) :=
    funext fun i => arrayX_sharpRows W β hβ p n y i
  rw [hx]
  simp only [arrayT_sharpRows, replayTargets_eq_targetTrace]
  exact gramSchmidt_coordinates_cast (rankCount_add p.a p.b n) _ _ _

theorem gramTolerance_le_three_quarters (K : ℕ) :
    1 / (16 * ((paddingDepth K + 1 : ℕ) : ℝ)^2) ≤ (3/4 : ℝ) := by
  have hd : (1 : ℝ) ≤ ((paddingDepth K + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * ((paddingDepth K + 1 : ℕ) : ℝ)^2)).mpr
  nlinarith

theorem replay_gram_small (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (y : SharpInput p n)
    (hy : sharpRows W β hβ p n y ∈ gramGood W β hβ p n) :
    ‖familyGram (replayTargetFamily W β hβ p n y) - 1‖ ≤ (3/4 : ℝ) := by
  rw [← arrayEA_sharpRows]
  exact (gramGood_blocks W β hβ p n (paperGrowingQueryMeshSize_pos p.a n hn) _ hy).1.trans
    (gramTolerance_le_three_quarters _)

theorem arrayCoefficients_eq_paper (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (y : SharpInput p n)
    (hy : sharpRows W β hβ p n y ∈ gramGood W β hβ p n) :
    arrayCoefficients (sharpRows W β hβ p n y) =
      WithLp.toLp 2 (paperSpinCoefficients (coarseRank p n) (coarseCount p n) n
        (M1.Target W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))
        (M1.Update (coarseMesh p n) (coarseRank p n) (coarseCount p n))
        (M1.ReplayInitial (coarseMesh p n) (coarseRank p n) (coarseCount p n)
          (sharpReplayInput p n y))
        (M1.ReplayQueriedNoise W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
          (sharpReplayInput p n y))
        (fun i => scalarHiddenSign (y.1 (Fin.cast (rankCount_add p.a p.b n) i)))) := by
  rw [arrayCoefficients_eq_replay, N13d.paperSpinCoefficients_eq_coordinates _ _ _ (Nat.cast_pos.mpr hn)]
  congr 1
  funext j
  exact (actualPaper_directionTrace_eq_gramSchmidtNormed _ _ _ _ _ _
    (Real.sqrt (n : ℝ))⁻¹ (by positivity) (replay_gram_small W β hβ p n hn y hy) j).symm

theorem arrayCoefficients_norm_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (y : SharpInput p n)
    (hy : sharpRows W β hβ p n y ∈ gramGood W β hβ p n) :
    ‖arrayCoefficients (sharpRows W β hβ p n y)‖ ≤ 1 := by
  rw [arrayCoefficients_eq_paper W β hβ p n hn y hy]
  have hx : dot (signSpin (fun i => y.1 (Fin.cast (rankCount_add p.a p.b n) i)))
      (signSpin (fun i => y.1 (Fin.cast (rankCount_add p.a p.b n) i))) = (n : ℝ) :=
    (signSpin_norm_sq _).trans (congrArg (fun N : ℕ => (N : ℝ)) (rankCount_add p.a p.b n))
  have hb := actualPaper_coefficient_budget (coarseRank p n) (coarseCount p n) n
    (Nat.cast_pos.mpr hn)
    (M1.Target W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (M1.Update (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (M1.ReplayInitial (coarseMesh p n) (coarseRank p n) (coarseCount p n) (sharpReplayInput p n y))
    (M1.ReplayQueriedNoise W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
      (sharpReplayInput p n y)) _ hx
  exact norm_toLp_le_one_of_sum_sq_le _ hb

theorem sharpEnergy_and_variance (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n)
    (hpost : parisiEquilibriumPhysicalEndpoint β ≤
      growingQueryTime (coarseMesh p n) (coarseCount p n))
    (y : SharpInput p n) (hy : sharpRows W β hβ p n y ∈ gramGood W β hβ p n) :
    |sharpQueryEnergy W β hβ p n y - linearEnergy W β hβ (sharpRows W β hβ p n y)| ≤
      200 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ) *
        weightedSq W β hβ (sharpRows W β hβ p n y) ∧
    discardedVariance (sharpRows W β hβ p n y) ≤ (n : ℝ)⁻¹ *
      (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2) * (coarseMesh p n : ℝ) +
        180 * weightedSq W β hβ (sharpRows W β hβ p n y) +
        (actualParisiFullSusceptibilityExpected W β
          (growingQueryTime (coarseMesh p n) (coarseCount p n)))^2) := by
  have he := sharpQueryEnergy_weighted_estimate W β hβ p n hn y hy
  rw [← arrayCoefficients_eq_paper W β hβ p n hn y hy] at he
  refine ⟨he.2, ?_⟩
  have hδ := paperGrowingQueryMeshSize_pos p.a n hn
  have hH := (growingQueryTime_strictMono _ hδ).monotone (Nat.le_succ (coarseCount p n))
  have h := N13d.coefficientVariance_sharp_le n (Nat.cast_pos.mpr hn)
    (arrayCoefficients (sharpRows W β hβ p n y)) (rowS W β hβ p n)
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2) * (coarseMesh p n : ℝ))
    (6 * Real.sqrt (weightedSq W β hβ (sharpRows W β hβ p n y)))
    (actualParisiFullSusceptibilityExpected W β
      (growingQueryTime (coarseMesh p n) (coarseCount p n)))
    (by positivity) (by positivity) (actualParisiFullSusceptibilityExpected_nonneg _ _ _)
    (arrayCoefficients_norm_le_one W β hβ p n hn y hy) he.1
    (N13d.populationTargetSpin_growing_coordinate_sq_le W W β hβ _ hδ _ _ _ hH)
    (N13d.populationTargetSpin_norm_sq_eq_defect W W β hβ _ (growingQueryTime_strictMono _ hδ)
      rfl _ _ _ hH hpost)
  simpa only [discardedVariance, mul_pow, Real.sq_sqrt (weightedSq_nonneg W β hβ _),
    show (5 : ℝ) * 6^2 = 180 by norm_num, ← mul_assoc] using h

end SKConstants.Completion.NL1
