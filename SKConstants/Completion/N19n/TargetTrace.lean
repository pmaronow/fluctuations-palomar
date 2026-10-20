module

public import SKConstants.Completion.LM1b.SourceTrace
public import SKConstants.Completion.N19.Stability
public import SKConstants.Completion.N19.Gram
public import SKConstants.Completion.N13a.Node
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators Matrix.Norms.L2Operator
namespace SKConstants.Completion.N19n
open GaussianProposal M1 N19 Blueprint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type} [MeasurableSpace Ω]

theorem growing_targetTrace_eq_terminal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ)
    (s : ScalarGrowingPaperPast (M1.Horizon δ q) δ (r₀+q))
    (z : StoppedNoise (Fin (r₀+q)) q) (e : Fin q) (i : Fin (r₀+q)) :
    paperTargetTrace r₀ (r₀+q) (M1.Target W β hβ δ r₀ q) (M1.Update δ r₀ q)
      q (s,1) z e i =
    (let f := fun t : ℝ≥0 => scalarMeshPaperObservation (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (M1.Horizon δ q)
      (growingQueryDuration δ) (growingQueryTime δ) (r₀+q)
      (proposalTerminalPast (M1.Update δ r₀ q) q s z) i
      (projIcc 0 (M1.Horizon δ q : ℝ) (M1.Horizon δ q).coe_nonneg t)
     (actualParisiFullMagnetization β (growingQueryTime δ (e.val+1)) (f (growingQueryTime δ (e.val+1))) -
      actualParisiFullMagnetization β (growingQueryTime δ e.val) (f (growingQueryTime δ e.val))) /
      (actualParisiPosteriorIntervalScale W β (growingQueryTime δ e.val)
        (growingQueryTime δ (e.val+1)) : ℝ)) := by
  let a := paperScalarPastTrace r₀ (Size r₀ q) (Target W β hβ δ r₀ q) (Update δ r₀ q)
    q (s, 1) z e.castSucc
  have hm := (growingQueryTime_strictMono δ hδ).monotone
  have htH : growingQueryTime δ (e.val+1) ≤ Horizon δ q := hm (by exact Nat.succ_le_succ e.isLt.le)
  have haH : growingQueryTime δ e.val ≤ Horizon δ q := (hm (Nat.le_succ e.val)).trans htH
  have hp : ScalarMeshPastPrefixEq (Horizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
      (Size r₀ q) (growingQueryTime δ (e.val+1)) a (proposalTerminalPast (Update δ r₀ q) q s z) := by
    have hs : a.1 = (proposalTerminalPast (Update δ r₀ q) q s z).1 :=
      (scalarMeshSourceTrace_static _ _ _ r₀ (Size r₀ q) q (Target W β hβ δ r₀ q) q
        (s, 1) z e.castSucc).trans
        (scalarMeshSourceRun_static _ _ _ (Size r₀ q) q q s z).symm
    exact ⟨congrArg Prod.fst hs, congrArg (fun x => x.2.2) hs,
      fun i u hu => scalarMeshSourceTrace_prefix (Horizon δ q) (growingQueryDuration δ)
        (growingQueryTime δ) hm r₀ (Size r₀ q) q (Target W β hβ δ r₀ q)
        q le_rfl (s,1) z e.castSucc i u (by simpa using hu),
      fun i u _ => congrArg (fun c : ScalarContinuousPath (Horizon δ q) => c u)
        (congrFun (congrArg (fun x => x.2.1) hs) i)⟩
  have he : q-(q-1-e.val) = e.val+1 := by omega
  have hv : q-(q-1-e.val+1) = e.val := by omega
  have hT := congrFun (scalarMeshPaperTarget_eq_of_prefix (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (actualParisiFullMagnetization β)
    (scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β) (growingQueryTime δ))
    (Horizon δ q) (growingQueryDuration δ) (growingQueryTime δ) (Size r₀ q) q (q-1-e.val)
    (growingQueryTime δ (e.val+1)) htH a (proposalTerminalPast (Update δ r₀ q) q s z) hp
    (by rw [he]) (by rw [hv]; exact hm (Nat.le_succ _))) i
  change paperTargetTrace _ _ _ _ _ _ _ _ _ = _
  rw [paperTargetTrace_eq_current_state]
  change Target W β hβ δ r₀ q (q-1-e.val) a i = _
  change scalarMeshPaperTarget _ _ _ _ _ _ _ _ _ _ _ _ _ a i = _
  rw [hT]
  dsimp only [scalarMeshPaperTarget, scalarMeshPaperQueryTime]
  rw [he, hv, actualParisiGrowingIncrementScale_eq_posterior W β hβ δ hδ (e.val+1) (by omega)]
  simp only [Nat.add_sub_cancel]

theorem replay_targetTrace_eq_magIncrement (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ)
    (M : Matrix (Fin (r+q)) (Fin (r+q)) ℝ) (a : ReplayAux δ r q)
    (j : Fin q) (i : Fin (r+q)) :
    paperMatrixQueryTargetTrace r (r+q) ((r+q : ℕ) : ℝ)
      (actualParisiGrowingSourceTarget W β hβ δ r q)
      (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (r+q) q) q
      (replayStart δ r q a,1) (paperCompletionReplayNoise (r+q) q a.2.1) M j i =
    (replayMag W β hβ δ r q (growingQueryTime δ (j.val+1)) M a i -
      replayMag W β hβ δ r q (growingQueryTime δ j.val) M a i) /
      (actualParisiPosteriorIntervalScale W β (growingQueryTime δ j.val)
        (growingQueryTime δ (j.val+1)) : ℝ) := by
  simpa only [replayMag_eq_observation, replayPast, paperMatrixQueryTargetTrace,
    paperMatrixQueryRun_eq_replayed_terminal, Target, Update] using
    growing_targetTrace_eq_terminal W β hβ δ hδ r q (replayStart δ r q a)
      (paperMatrixQueryNoiseRun r (r+q) ((r+q : ℕ) : ℝ)
        (actualParisiGrowingSourceTarget W β hβ δ r q)
        (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (r+q) q) q
        (replayStart δ r q a,1) (paperCompletionReplayNoise (r+q) q a.2.1) M) j i

theorem replayTargetGram_eq_posteriorGram (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ)
    (M : Matrix (Fin (r+q)) (Fin (r+q)) ℝ) (a : ReplayAux δ r q) :
    replayTargetGram W β hβ δ r q (Real.sqrt (r+q : ℕ))⁻¹ M a =
      familyGram (fieldPosteriorColumns W β (M1.Horizon δ q) (growingQueryTime δ) q (r+q)
        (fun j hj => (M1.growingQueryTime_monotone δ) (by omega))
        (replayFieldRows W β hβ δ r q (replayInput M a))) := by
  unfold replayTargetGram fieldPosteriorColumns
  congr 1
  funext j
  congr 1
  apply congrArg (WithLp.toLp 2)
  funext i
  exact replay_targetTrace_eq_magIncrement W β hβ δ hδ r q M a j i

end SKConstants.Completion.N19n
