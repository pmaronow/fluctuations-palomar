module

public import SKConstants.Completion.N19n.TargetTrace
public import SKConstants.Completion.N19.Node
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators Matrix.Norms.L2Operator
namespace SKConstants.Completion.N19n
open GaussianProposal Blueprint N19
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type} [MeasurableSpace Ω]

theorem familyGram_fin_cast {k n m : ℕ} (h : n = m)
    (u : Fin k → EuclideanSpace ℝ (Fin n)) (v : Fin k → EuclideanSpace ℝ (Fin m))
    (he : ∀ j i, u j (Fin.cast h.symm i) = v j i) : familyGram u = familyGram v := by
  subst m
  have huv : u = v := by
    funext j
    ext i
    exact he j i
  rw [huv]

theorem coarsePrefix_targetGram_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (rf qf rb qb : ℕ)
    (hdim : rf+qf = rb+qb) (hq : qb ≤ qf)
    (M : Matrix (Fin (rf+qf)) (Fin (rf+qf)) ℝ) (a : ReplayAux δ rf qf) :
    replayTargetGram W β hβ δ rb qb (Real.sqrt (rb+qb : ℕ))⁻¹
      (castMatrix hdim.symm M) (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq a) =
    familyGram (fieldPosteriorColumns W β (M1.Horizon δ qf) (growingQueryTime δ)
      qb (rf+qf) (fun j hj => (M1.growingQueryTime_monotone δ) (by omega))
      (replayFieldRows W β hβ δ rf qf (replayInput M a))) := by
  rw [replayTargetGram_eq_posteriorGram W β hβ δ hδ]
  symm
  apply familyGram_fin_cast hdim
  intro j i
  change (Real.sqrt (rf+qf : ℕ))⁻¹ *
      ((replayMag W β hβ δ rf qf (growingQueryTime δ (j.val+1)) M a (Fin.cast hdim.symm i) -
        replayMag W β hβ δ rf qf (growingQueryTime δ j.val) M a (Fin.cast hdim.symm i)) / _) =
    (Real.sqrt (rb+qb : ℕ))⁻¹ *
      ((replayMag W β hβ δ rb qb (growingQueryTime δ (j.val+1)) (castMatrix hdim.symm M)
          (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq a) i -
        replayMag W β hβ δ rb qb (growingQueryTime δ j.val) (castMatrix hdim.symm M)
          (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq a) i) / _)
  have hroot : (Real.sqrt (rf+qf : ℕ))⁻¹ = (Real.sqrt (rb+qb : ℕ))⁻¹ := by rw [hdim]
  rw [hroot]
  have hfield (k : ℕ) (hk : k ≤ qb+1) := congrFun
    (N13a.coarsePrefix_replayMag W β hβ δ rf qf rb qb hdim hq M a
      (growingQueryTime δ k) ((M1.growingQueryTime_monotone δ) hk)) i
  rw [hfield (j.val+1) (by omega), hfield j.val (by omega)]

def coarseReplayMatrix (p : Parameters) (n : ℕ) (g : Prim n) :=
  castMatrix (rankCount_add p.a p.b n) (physical n g)

def coarseReplayAux (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f) (a : FineAux p n) :=
  N13a.coarsePrefix_fineAux p n (queryCount_mono p.a p.b p.f hbf n) a

theorem coarseReplay_targetGram_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hn : 0 < n) (hbf : p.b ≤ p.f) (y : RunInput p n) :
    replayTargetGram W β hβ (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
      (Real.sqrt (rankCount p.a p.b n + queryCount p.a p.b n : ℕ))⁻¹
      (coarseReplayMatrix p n y.1) (coarseReplayAux p n hbf y.2.1) =
      familyGram (coarsePosteriorColumns W β hβ p n hbf y) := by
  exact coarsePrefix_targetGram_eq W β hβ (meshSize p.a n)
    (paperGrowingQueryMeshSize_pos p.a n hn)
    (rankCount p.a p.f n) (queryCount p.a p.f n)
    (rankCount p.a p.b n) (queryCount p.a p.b n) (N13a.coarsePrefix_dimension p n)
    (queryCount_mono p.a p.b p.f hbf n)
    (castMatrix (rankCount_add p.a p.f n) (physical n y.1)) y.2.1

theorem magGap_castVec {n m : ℕ} (h : n = m) (u v : Fin n → ℝ) :
    magGap (castVec h u) (castVec h v) = magGap u v := by
  subst m
  rfl

theorem coarseMag_gap_eq_replay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f) (g g' : Prim n) (a a' : FineAux p n) :
    magGap (coarseMag W β hβ p n g a) (coarseMag W β hβ p n g' a') =
      magGap (replayMag W β hβ (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
        (readoutTime p.a p.b n) (coarseReplayMatrix p n g) (coarseReplayAux p n hbf a))
      (replayMag W β hβ (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
        (readoutTime p.a p.b n) (coarseReplayMatrix p n g') (coarseReplayAux p n hbf a')) := by
  unfold coarseMag
  rw [N13a.coarsePrefix_runMag W β hβ p n (queryCount_mono p.a p.b p.f hbf n)
      g a _ le_rfl,
    N13a.coarsePrefix_runMag W β hβ p n (queryCount_mono p.a p.b p.f hbf n)
      g' a' _ le_rfl,
    magGap_castVec]
  rfl

end SKConstants.Completion.N19n
