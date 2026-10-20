module

public import SKConstants.Completion.Blueprint.Nodes
public import SKConstants.ScalarMatrixQueryPathStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology Matrix.Norms.L2Operator BigOperators

namespace SKConstants.Completion.N19
open Blueprint GaussianProposal SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualParisiFullMagnetization_lipschitz (β v : ℝ) :
    LipschitzWith 1 (actualParisiFullMagnetization β v) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (actualParisiFullMagnetization_hasDerivAt β v x).differentiableAt)
  intro x
  rw [(actualParisiFullMagnetization_hasDerivAt β v x).deriv]
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs]
  have h := actualParisiFullMagnetization_curvature_bounds β v x
  rw [abs_of_nonneg h.2.1]
  nlinarith [h.2.2]

def replayStart (δ : ℝ≥0) (r q : ℕ) (a : ReplayAux δ r q) :
    ScalarGrowingPaperPast (scalarGrowingSourceHorizon δ q) δ (r + q) :=
  scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (r + q) (a.2.2, a.1)

def replayPast (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ)
    (M : Matrix (Fin (r + q)) (Fin (r + q)) ℝ) (a : ReplayAux δ r q) :=
  paperMatrixQueryRun r (r + q) ((r + q : ℕ) : ℝ)
    (actualParisiGrowingSourceTarget W β hβ δ r q)
    (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (r + q) q) q
    (replayStart δ r q a, 1) (paperCompletionReplayNoise (r + q) q a.2.1) M

def replayTargetGram (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ)
    (c : ℝ) (M : Matrix (Fin (r + q)) (Fin (r + q)) ℝ) (a : ReplayAux δ r q) :=
  familyGram (fun j => c • WithLp.toLp 2
    (paperMatrixQueryTargetTrace r (r + q) ((r + q : ℕ) : ℝ)
      (actualParisiGrowingSourceTarget W β hβ δ r q)
      (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (r + q) q) q
      (replayStart δ r q a, 1) (paperCompletionReplayNoise (r + q) q a.2.1) M j))

theorem actual_replayPathGap_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (a b : ReplayAux δ r q)
    (M M' : Matrix (Fin (r + q)) (Fin (r + q)) ℝ)
    (c η C A sMin : ℝ) (hc : 0 < c) (hη : 0 ≤ η) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hsMin : 0 < sMin) (hcN : c * Real.sqrt (r + q : ℕ) ≤ 1)
    (hD : ∀ i, ‖a.2.2 i - b.2.2 i‖ ≤ η)
    (hInitial : scalarMeshPathGap (replayStart δ r q a) (replayStart δ r q b) ≤ η)
    (hfC : scalarStieltjesPathBound (actualParisiNegativeRhoStieltjes W β hβ)
      (scalarGrowingSourceHorizon δ q) ≤ C)
    (hgC : scalarStieltjesPathBound (actualParisiSigmaStieltjes W β hβ)
      (scalarGrowingSourceHorizon δ q) ≤ C)
    (hδ : ∀ j : Fin q, 0 < growingQueryDuration δ (j.val + 1) ∧
      growingQueryDuration δ (j.val + 1) ≤ 1)
    (hscale : ∀ j : Fin q, sMin ≤
      scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
        (growingQueryTime δ) (j.val + 1))
    (hbridge : ∀ j : Fin q, (∑ i, ‖a.1.2 (j.val + 1) i - b.1.2 (j.val + 1) i‖) ≤ η)
    (hM : ‖M - M'‖ ≤ η) (hM' : ‖M'‖ ≤ A)
    (hz : ∀ j : Fin q, ‖WithLp.toLp 2 (fun i => paperNoiseTrace (r + q) q
      (paperCompletionReplayNoise (r + q) q a.2.1) j (.inl i))‖ ≤ A)
    (hzw : ∀ j : Fin q, ‖WithLp.toLp 2 (fun i =>
      paperNoiseTrace (r + q) q (paperCompletionReplayNoise (r + q) q a.2.1) j (.inl i) -
      paperNoiseTrace (r + q) q (paperCompletionReplayNoise (r + q) q b.2.1) j (.inl i))‖ ≤ η)
    (hGram : ‖replayTargetGram W β hβ δ r q c M a - 1‖ ≤ (3 / 4 : ℝ))
    (hGram' : ‖replayTargetGram W β hβ δ r q c M' b - 1‖ ≤ (3 / 4 : ℝ)) :
    scalarMeshPathGap (replayPast W β hβ δ r q M a) (replayPast W β hβ δ r q M' b) ≤
      2 * η * (coupledScalarQueryGapFactor (r + q) q
        (scalarQueryTargetGapFactor (actualParisiFullScalarDrift β) (scalarGrowingSourceHorizon δ q)
          C sMin) A) ^ q := by
  exact scalarMeshMatrixQuery_pathGap_le (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (actualParisiFullMagnetization β) (actualParisiFullMagnetization_lipschitz β)
    (scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
      (growingQueryTime δ)) (scalarGrowingSourceHorizon δ q)
    (growingQueryDuration δ) (growingQueryTime δ) r q
    (replayStart δ r q a) (replayStart δ r q b)
    (paperCompletionReplayNoise (r + q) q a.2.1) (paperCompletionReplayNoise (r + q) q b.2.1)
    M M' c η C A sMin hc hη hC hA hsMin hcN (by intro i; simpa [replayStart, scalarGrowingPaperInitialState])
    hD hInitial hfC hgC hδ hscale hbridge hM hM' hz hzw hGram hGram'

theorem replayMag_eq_observation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (v : ℝ≥0)
    (M : Matrix (Fin (r + q)) (Fin (r + q)) ℝ) (a : ReplayAux δ r q) :
    replayMag W β hβ δ r q v M a = fun i => actualParisiFullMagnetization β v
      (scalarMeshPaperObservation (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ)
        (scalarGrowingSourceHorizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
        (r + q) (replayPast W β hβ δ r q M a) i
        (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg v)) := by
  unfold Blueprint.replayMag actualParisiGrowingReplayField scalarGrowingReplayField
  simp only [replayPast, actualParisiGrowingSourceTarget, replayStart, replayInput, Nat.cast_add]

theorem replayPast_static (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (M : Matrix (Fin (r + q)) (Fin (r + q)) ℝ)
    (a : ReplayAux δ r q) : (replayPast W β hβ δ r q M a).1 = (replayStart δ r q a).1 := by
  exact scalarMeshMatrixQueryRun_static (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (actualParisiFullMagnetization β)
    (scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
      (growingQueryTime δ)) (scalarGrowingSourceHorizon δ q) (growingQueryDuration δ)
    (growingQueryTime δ) r (r + q) q q ((r + q : ℕ) : ℝ)
    (replayStart δ r q a, 1) (paperCompletionReplayNoise (r + q) q a.2.1) M

theorem replayMag_gap_of_pathGap (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r q : ℕ) (v : ℝ≥0) (a b : ReplayAux δ r q)
    (M M' : Matrix (Fin (r + q)) (Fin (r + q)) ℝ) (η C B : ℝ)
    (hC : 0 ≤ C)
    (hD : ∀ i, ‖a.2.2 i - b.2.2 i‖ ≤ η)
    (hfC : scalarStieltjesPathBound (actualParisiNegativeRhoStieltjes W β hβ)
      (scalarGrowingSourceHorizon δ q) ≤ C)
    (hgC : scalarStieltjesPathBound (actualParisiSigmaStieltjes W β hβ)
      (scalarGrowingSourceHorizon δ q) ≤ C)
    (hpath : scalarMeshPathGap (replayPast W β hβ δ r q M a)
      (replayPast W β hβ δ r q M' b) ≤ B) :
    magGap (replayMag W β hβ δ r q v M a) (replayMag W β hβ δ r q v M' b) ≤
      (r + q : ℕ) * (2 * C * (B + η) *
        Real.exp ((actualParisiFullScalarDrift β).rate * (scalarGrowingSourceHorizon δ q))) ^ 2 := by
  let s := replayPast W β hβ δ r q M a
  let t := replayPast W β hβ δ r q M' b
  have hs : s.1 = (replayStart δ r q a).1 :=
    replayPast_static W β hβ δ r q M a
  have ht : t.1 = (replayStart δ r q b).1 :=
    replayPast_static W β hβ δ r q M' b
  rw [replayMag_eq_observation, replayMag_eq_observation]
  unfold magGap
  have he (i : Fin (r + q)) : |actualParisiFullMagnetization β v
      (scalarMeshPaperObservation (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ)
        (scalarGrowingSourceHorizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
        (r + q) s i (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg v)) -
      actualParisiFullMagnetization β v
      (scalarMeshPaperObservation (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ)
        (scalarGrowingSourceHorizon δ q) (growingQueryDuration δ) (growingQueryTime δ)
        (r + q) t i (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg v))| ≤
      2 * C * (B + η) * Real.exp ((actualParisiFullScalarDrift β).rate * (scalarGrowingSourceHorizon δ q)) := by
    have hl := (actualParisiFullMagnetization_lipschitz β v).dist_le_mul
      (scalarMeshPaperObservation (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) (scalarGrowingSourceHorizon δ q)
        (growingQueryDuration δ) (growingQueryTime δ) (r + q) s i
        (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg v))
      (scalarMeshPaperObservation (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) (scalarGrowingSourceHorizon δ q)
        (growingQueryDuration δ) (growingQueryTime δ) (r + q) t i
        (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg v))
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hl
    have hp := scalarTwoDriverPicardPath_norm_difference_le (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ)
      (scalarGrowingSourceHorizon δ q) (s.1.1 i) (t.1.1 i) (s.2 i) (t.2 i) (s.1.2.1 i) (t.1.2.1 i)
    have hv := (scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (scalarGrowingSourceHorizon δ q)
      (s.1.1 i, (s.2 i, s.1.2.1 i)) -
      scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (scalarGrowingSourceHorizon δ q)
      (t.1.1 i, (t.2 i, t.1.2.1 i))).norm_coe_le_norm
        (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg v)
    have hs0 : s.1.1 i = 0 := by rw [hs]; rfl
    have ht0 : t.1.1 i = 0 := by rw [ht]; rfl
    have hDD : ‖s.1.2.1 i - t.1.2.1 i‖ ≤ η := by rw [hs, ht]; exact hD i
    have hBB := (scalarMeshPathGap_coord_le s t i).trans hpath
    conv_rhs at hp => rw [hs0, ht0, sub_self, abs_zero, zero_add]
    have hfc := mul_le_mul hfC hBB (norm_nonneg _) hC
    have hgc := mul_le_mul hgC hDD (norm_nonneg _) hC
    refine (hl.trans hv).trans (hp.trans ?_)
    nlinarith [mul_le_mul_of_nonneg_right (add_le_add hfc hgc)
      (Real.exp_pos ((actualParisiFullScalarDrift β).rate * (scalarGrowingSourceHorizon δ q))).le]
  calc
    _ ≤ ∑ _i : Fin (r + q), (2 * C * (B + η) *
        Real.exp ((actualParisiFullScalarDrift β).rate * (scalarGrowingSourceHorizon δ q))) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he i) 2
    _ = _ := by simp

end SKConstants.Completion.N19
