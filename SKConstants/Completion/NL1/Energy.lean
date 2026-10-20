module

public import SKConstants.Completion.NL1.Coordinates
public import SKConstants.Completion.N13d.CoarseSchedule
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal Topology

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5 LGram N13A LM5

variable {Ω : Type} [MeasurableSpace Ω]

theorem arrayEA_eq_sampleGram {p : Parameters} {n : ℕ} (z : RowArray p n) :
    arrayEA z = familyGram (fun j => sampleColumn z (posteriorIndex _ j)) - 1 := by
  unfold arrayEA
  congr 1
  ext i j
  exact (sampleColumn_inner z _ _).symm

theorem arrayEH_eq_sampleCross (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {p : Parameters} {n : ℕ} (z : RowArray p n) :
    arrayEH W β hβ z =
      familyCross (fun j => sampleColumn z (posteriorIndex _ j))
        (fun j => sampleColumn z (queryIndex _ j)) - rowH0 W β hβ p n := by
  unfold arrayEH
  congr 1
  ext i j
  exact (sampleColumn_inner z _ _).symm

theorem gramGood_blocks (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hδ : 0 < coarseMesh p n) (z : RowArray p n)
    (hz : z ∈ gramGood W β hβ p n) :
    ‖arrayEA z‖ ≤ 1 / (16 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2) ∧
    ‖arrayEH W β hβ z‖ ≤ 1 / (16 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2) := by
  have h := rowGramEvent_blocks (rowPopulation W β hβ p n)
    (posteriorIndex (coarseCount p n)) (queryIndex (coarseCount p n))
    (posteriorIndex_injective _) (queryIndex_injective _) (spinIndex _) z _ hz
    (mixedPopulation_target_block W W β hβ _ (growingQueryTime_strictMono _ hδ) _ _ _)
  rw [arrayEA_eq_sampleGram, arrayEH_eq_sampleCross]
  exact ⟨h.1, h.2.1⟩

theorem weightedSq_eq_replay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    weightedSq W β hβ (sharpRows W β hβ p n y) =
      sevenErrorSumDim (paddingDepth (coarseCount p n))
        (coarseCount p n + paddingCount (coarseCount p n)) (padding_size _)
        (padMatrix _ (familyGram (replayTargetFamily W β hβ p n y) - 1) 0)
        (padMatrix _ (familyCross (replayTargetFamily W β hβ p n y)
          (replayQueryFamily W β hβ p n y) - rowH0 W β hβ p n) 0)
        (padVector _ (rowS W β hβ p n))
        (padVector _ (familyCoordinates (replayTargetFamily W β hβ p n y)
          (replaySpinVector p n y) - rowS W β hβ p n))
        (padVector _ (rowB W β hβ p n))
        (padVector _ (familyCoordinates (replayQueryFamily W β hβ p n y)
          (replaySpinVector p n y) - rowB W β hβ p n)) := by
  simp only [weightedSq, arrayEA_sharpRows, arrayEH_sharpRows,
    arrayEq_sharpRows, arrayEv_sharpRows]

theorem weightedSq_nonneg (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    {p : Parameters} {n : ℕ} (z : RowArray p n) : 0 ≤ weightedSq W β hβ z :=
  N13d.sevenErrorSumDim_nonneg _ _ _ _ _ _ _ _ _

theorem sharpQueryEnergy_weighted_estimate (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (y : SharpInput p n)
    (hy : sharpRows W β hβ p n y ∈ gramGood W β hβ p n) :
    ‖WithLp.toLp 2 (paperSpinCoefficients (coarseRank p n) (coarseCount p n) n
        (M1.Target W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))
        (M1.Update (coarseMesh p n) (coarseRank p n) (coarseCount p n))
        (M1.ReplayInitial (coarseMesh p n) (coarseRank p n) (coarseCount p n)
          (sharpReplayInput p n y))
        (M1.ReplayQueriedNoise W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
          (sharpReplayInput p n y))
        (fun i => scalarHiddenSign (y.1 (Fin.cast (rankCount_add p.a p.b n) i)))) -
        rowS W β hβ p n‖ ≤ 6 * Real.sqrt (weightedSq W β hβ (sharpRows W β hβ p n y)) ∧
    |sharpQueryEnergy W β hβ p n y - linearEnergy W β hβ (sharpRows W β hβ p n y)| ≤
      200 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ) *
        weightedSq W β hβ (sharpRows W β hβ p n y) := by
  have hδ := paperGrowingQueryMeshSize_pos p.a n hn
  have h := gramGood_blocks W β hβ p n hδ _ hy
  rw [arrayEA_sharpRows] at h
  rw [arrayEH_sharpRows] at h
  have hd : (0 : ℝ) < ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ) := by positivity
  have hsmall : 16 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2 *
      (1 / (16 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2)) ≤ 1 := by
    rw [mul_one_div_cancel (by positivity :
      (16 : ℝ) * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2 ≠ 0)]
  have he := N13d.actualPaper_query_energy_weighted_estimate (coarseRank p n) (coarseCount p n)
    (paddingDepth (coarseCount p n)) (paddingCount (coarseCount p n)) (padding_size _)
    n (1 / (16 * ((paddingDepth (coarseCount p n) + 1 : ℕ) : ℝ)^2)) (Nat.cast_pos.mpr hn)
    (M1.Target W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (M1.Update (coarseMesh p n) (coarseRank p n) (coarseCount p n))
    (M1.ReplayInitial (coarseMesh p n) (coarseRank p n) (coarseCount p n) (sharpReplayInput p n y))
    (M1.ReplayQueriedNoise W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
      (sharpReplayInput p n y))
    (fun i => scalarHiddenSign (y.1 (Fin.cast (rankCount_add p.a p.b n) i)))
    (rowS W β hβ p n) (rowB W β hβ p n) (rowH0 W β hβ p n)
    (by positivity) hsmall h.1
    (populationCross_shifted_upper W W β hβ _ (growingQueryTime_strictMono _ hδ).monotone _ _) h.2
  change _ ∧ |sharpQueryEnergy W β hβ p n y - inner (𝕜 := ℝ) _ _ -
    N13e.energyLinearPart _ _ _ _ _ _| ≤ _ at he
  simpa only [linearEnergy, arrayEA_sharpRows, arrayEH_sharpRows,
    arrayEq_sharpRows, arrayEv_sharpRows, weightedSq_eq_replay, sub_add_eq_sub_sub] using he

end SKConstants.Completion.NL1
