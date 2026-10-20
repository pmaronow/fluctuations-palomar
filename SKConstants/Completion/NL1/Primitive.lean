module

public import SKConstants.Completion.NL1.JointLaw
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5 LGram N13A LM5

variable {Ω : Type} [MeasurableSpace Ω]

theorem quadraticEnergy_cast (m n : ℕ) (h : m = n) (x : Spin n)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    quadraticEnergy (m : ℝ) (signSpin (fun i => x (Fin.cast h i))) (castMatrix h A) =
      quadraticHamiltonian A x / n := by
  subst n
  have hs (i : Fin m) : signSpin x i = signedSpin x i := by
    simp only [signSpin, scalarHiddenSign, signedSpin]
  simp only [castMatrix, Fin.cast_refl, id_eq, quadraticEnergy, quadraticHamiltonian,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, hs, div_eq_mul_inv]
  ring

theorem replayRows_sharpToReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    (fun i : Fin n => replayRows W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
      (T0.sharpToReplay p n y) (Fin.cast (rankCount_add p.a p.b n).symm i)) =
      sharpRows W β hβ p n y := by
  funext i
  simp only [replayRows, T0.sharpToReplay, sharpRows, Fin.cast_cast, Fin.cast_refl, id_eq]

theorem replayQueryEnergy_sharpToReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    replayQueryEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
      (T0.sharpToReplay p n y) = sharpQueryEnergy W β hβ p n y := by
  unfold replayQueryEnergy
  have hN : ((coarseRank p n + coarseCount p n : ℕ) : ℝ) = (n : ℝ) :=
    congrArg (fun N : ℕ => (N : ℝ)) (rankCount_add p.a p.b n)
  rw [hN]
  rfl

theorem replayDiscardedEnergy_sharpToReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (y : SharpInput p n) :
    replayDiscardedEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)
      (T0.sharpToReplay p n y) = sharpDiscarded W β hβ p n y := by
  rw [replayDiscardedEnergy, replayQueryEnergy_sharpToReplay]
  change quadraticEnergy _ (signSpin (fun i => y.1 (Fin.cast (rankCount_add p.a p.b n) i)))
    (castMatrix (rankCount_add p.a p.b n) (physical n y.2.1)) - _ = _
  rw [quadraticEnergy_cast]
  rfl

def sourceSharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ)
    (u : (Fin (coarseRank p n + coarseCount p n) → Bool) ×
      M1.SourceInput (coarseMesh p n) (coarseRank p n) (coarseCount p n)) : RowArray p n :=
  fun i => literalSourceRows W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) u
    (Fin.cast (rankCount_add p.a p.b n).symm i)

theorem source_sharp_joint_energy_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) :
    (M1.SourceLinkedLaw W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n)).map
      (fun u => (sourceSharpRows W β hβ p n u,
        sourceQueryEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) u,
        growingSourceDiscardedEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) u)) =
    (sharpLinkedLaw W β hβ p n).map (fun y =>
      (sharpRows W β hβ p n y, sharpQueryEnergy W β hβ p n y, sharpDiscarded W β hβ p n y)) := by
  let δ := coarseMesh p n
  let r := coarseRank p n
  let K := coarseCount p n
  let F := fun u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K =>
    ((fun i : Fin n => replayRows W β hβ δ r K u (Fin.cast (rankCount_add p.a p.b n).symm i)),
      replayQueryEnergy W β hβ δ r K u, replayDiscardedEnergy W β hβ δ r K u)
  have hF : Measurable F := (Measurable.of_eval fun i =>
    (measurable_pi_apply _).comp (measurable_replayRows W β hβ δ r K)).prodMk
      ((measurable_replayQueryEnergy W β hβ δ r K).prodMk
        (measurable_replayDiscardedEnergy W β hβ δ r K))
  have hN : 0 < r+K := by simpa only [r, K, coarseRank, coarseCount, rankCount_add] using hn
  have hs : (fun u => (sourceSharpRows W β hβ p n u,
      sourceQueryEnergy W β hβ δ r K u, growingSourceDiscardedEnergy W β hβ δ r K u)) =
      F ∘ (fun u => (u.1, M1.ToReplay W β hβ δ r K u.2)) := by
    funext u
    simp only [F, Function.comp_apply, replayRows_toReplay W β hβ δ r K hN,
      replayQueryEnergy_toReplay W β hβ δ r K hN,
      replayDiscardedEnergy_toReplay W β hβ δ r K hN, sourceSharpRows]
    rfl
  have hp : F ∘ T0.sharpToReplay p n = fun y =>
      (sharpRows W β hβ p n y, sharpQueryEnergy W β hβ p n y, sharpDiscarded W β hβ p n y) := by
    funext y
    exact Prod.ext (replayRows_sharpToReplay W β hβ p n y)
      (Prod.ext (replayQueryEnergy_sharpToReplay W β hβ p n y)
        (replayDiscardedEnergy_sharpToReplay W β hβ p n y))
  have hmap : Measurable (fun u : (Fin (r+K) → Bool) × M1.SourceInput δ r K =>
      (u.1, M1.ToReplay W β hβ δ r K u.2)) :=
    measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ r K).comp measurable_snd)
  rw [hs, ← Measure.map_map hF hmap, M1.growingSource_toReplay_linked_law W β hβ δ r K hN,
    ← hp, ← Measure.map_map hF (T0.measurable_sharpToReplay p n), T0.sharpToReplay_linked_law]

theorem measurable_sourceSharpRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (sourceSharpRows W β hβ p n) :=
  Measurable.of_eval fun i => (measurable_pi_apply _).comp
    (measurable_literalSourceRows W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n))

theorem measurable_sourceSharpJointEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) :
    Measurable (fun u => (sourceSharpRows W β hβ p n u,
      sourceQueryEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) u,
      growingSourceDiscardedEnergy W β hβ (coarseMesh p n) (coarseRank p n) (coarseCount p n) u)) := by
  let δ := coarseMesh p n
  let r := coarseRank p n
  let K := coarseCount p n
  have hN : 0 < r+K := by simpa only [r, K, coarseRank, coarseCount, rankCount_add] using hn
  have hmap : Measurable (fun u : (Fin (r+K) → Bool) × M1.SourceInput δ r K =>
      (u.1, M1.ToReplay W β hβ δ r K u.2)) :=
    measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ r K).comp measurable_snd)
  have hq := (measurable_replayQueryEnergy W β hβ δ r K).comp hmap
  have hz := (measurable_replayDiscardedEnergy W β hβ δ r K).comp hmap
  have hq' : Measurable (sourceQueryEnergy W β hβ δ r K) := by
    convert hq using 1
    funext u
    exact (replayQueryEnergy_toReplay W β hβ δ r K hN u).symm
  have hz' : Measurable (growingSourceDiscardedEnergy W β hβ δ r K) := by
    convert hz using 1
    funext u
    exact (replayDiscardedEnergy_toReplay W β hβ δ r K hN u).symm
  exact (measurable_sourceSharpRows W β hβ p n).prodMk (hq'.prodMk hz')

end SKConstants.Completion.NL1
