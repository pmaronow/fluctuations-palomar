module

public import SKConstants.Completion.N13A.EnergyMeasurable
public import SKConstants.Completion.N13d.RowEvents
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5 LGram N13A

variable {Ω : Type} [MeasurableSpace Ω]

theorem normalized_inner {m n : ℕ} (h : m = n) (x y : Fin m → ℝ) :
    inner (𝕜 := ℝ) ((Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 x)
      ((Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2 y) =
      (∑ i : Fin n, x (Fin.cast h.symm i) * y (Fin.cast h.symm i)) / (n : ℝ) := by
  subst n
  have hs : (Real.sqrt (m : ℝ))⁻¹ * (Real.sqrt (m : ℝ))⁻¹ = (m : ℝ)⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hs]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial, Fin.cast_refl, div_eq_inv_mul]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem replayTargets_eq_targetTrace (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (v : M1.ReplayInput δ r K) :
    M1.ReplayTargets W β hβ δ r K v =
      paperTargetTrace r (r+K) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
        (M1.ReplayInitial δ r K v, 1) (M1.ReplayQueriedNoise W β hβ δ r K v) :=
  paperMatrixQueryTargetTrace_eq r (r+K) ((r : ℝ) + K) _ _ K _ _ _

theorem replayEndpoints_eq_endpointTrace (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (v : M1.ReplayInput δ r K) :
    M1.ReplayEndpoints W β hβ δ r K v =
      fun j i => paperEndpointTrace (r+K) K
        (M1.ReplayQueriedNoise W β hβ δ r K v) j (.inl i) := by
  rw [N13d.paperEndpointTrace_eq_noiseTrace]
  rfl

theorem arrayT_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) (i : Fin n) (j : Fin (coarseCount p n)) :
    arrayT (sharpRows W β hβ p n y) i j =
      M1.ReplayTargets W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (sharpReplayInput p n y) j (Fin.cast (rankCount_add p.a p.b n).symm i) := by
  simp [arrayT, sharpRows, posteriorIndex]

theorem arrayG_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) (i : Fin n) (j : Fin (coarseCount p n)) :
    arrayG (sharpRows W β hβ p n y) i j =
      M1.ReplayEndpoints W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (sharpReplayInput p n y) j (Fin.cast (rankCount_add p.a p.b n).symm i) := by
  simp [arrayG, sharpRows, queryIndex]

theorem arrayX_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) (i : Fin n) :
    arrayX (sharpRows W β hβ p n y) i = scalarHiddenSign (y.1 i) := by
  simp [arrayX, sharpRows, spinIndex]

abbrev replayTargetFamily (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :=
  fun j => (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2
    (paperTargetTrace (coarseRank p n) (coarseRank p n + coarseCount p n)
      (M1.Target W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))
      (M1.Update (coarseMesh p n) (coarseRank p n) (coarseCount p n)) (coarseCount p n)
      (M1.ReplayInitial (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (sharpReplayInput p n y), 1)
      (M1.ReplayQueriedNoise W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (sharpReplayInput p n y)) j)

abbrev replayQueryFamily (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :=
  fun j : Fin (coarseCount p n) => (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2
    (fun i => paperEndpointTrace (coarseRank p n + coarseCount p n) (coarseCount p n)
      (M1.ReplayQueriedNoise W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
        (sharpReplayInput p n y)) j (.inl i))

abbrev replaySpinVector (p : Parameters) (n : ℕ) (y : SharpInput p n) :=
  (Real.sqrt (n : ℝ))⁻¹ • WithLp.toLp 2
    (fun i => scalarHiddenSign (y.1 (Fin.cast (rankCount_add p.a p.b n) i)))

theorem arrayEA_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    arrayEA (sharpRows W β hβ p n y) = familyGram (replayTargetFamily W β hβ p n y) - 1 := by
  unfold arrayEA
  congr 1
  ext j k
  dsimp only [familyGram, replayTargetFamily]
  rw [normalized_inner (rankCount_add p.a p.b n)]
  simp only [N13e.empiricalCross, arrayT_sharpRows, replayTargets_eq_targetTrace]

theorem arrayEH_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    arrayEH W β hβ (sharpRows W β hβ p n y) =
      familyCross (replayTargetFamily W β hβ p n y) (replayQueryFamily W β hβ p n y) -
        rowH0 W β hβ p n := by
  unfold arrayEH
  congr 1
  ext j k
  rw [familyCross, replayTargetFamily, replayQueryFamily, normalized_inner (rankCount_add p.a p.b n)]
  simp only [N13e.empiricalCross, arrayT_sharpRows, arrayG_sharpRows,
    replayTargets_eq_targetTrace, replayEndpoints_eq_endpointTrace]

theorem arrayEq_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    arrayEq W β hβ (sharpRows W β hβ p n y) =
      familyCoordinates (replayTargetFamily W β hβ p n y) (replaySpinVector p n y) -
        rowS W β hβ p n := by
  unfold arrayEq
  congr 1
  ext j
  change (∑ i, arrayT (sharpRows W β hβ p n y) i j *
    arrayX (sharpRows W β hβ p n y) i) / (n : ℝ) = _
  change _ = inner (𝕜 := ℝ) _ _
  dsimp only [replayTargetFamily, replaySpinVector]
  rw [normalized_inner (rankCount_add p.a p.b n)]
  simp only [arrayT_sharpRows, arrayX_sharpRows, replayTargets_eq_targetTrace,
    Fin.cast_cast, Fin.cast_refl, id_eq]

theorem arrayEv_sharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    arrayEv W β hβ (sharpRows W β hβ p n y) =
      familyCoordinates (replayQueryFamily W β hβ p n y) (replaySpinVector p n y) -
        rowB W β hβ p n := by
  unfold arrayEv
  congr 1
  ext j
  change (∑ i, arrayG (sharpRows W β hβ p n y) i j *
    arrayX (sharpRows W β hβ p n y) i) / (n : ℝ) = _
  change _ = inner (𝕜 := ℝ) _ _
  dsimp only [replayQueryFamily, replaySpinVector]
  rw [normalized_inner (rankCount_add p.a p.b n)]
  simp only [arrayG_sharpRows, arrayX_sharpRows, replayEndpoints_eq_endpointTrace,
    Fin.cast_cast, Fin.cast_refl, id_eq]

end SKConstants.Completion.NL1
