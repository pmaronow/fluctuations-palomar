module

public import SKConstants.Completion.N19n.PolynomialCoefficients
public import SKConstants.Completion.N19n.GridBound
public import SKConstants.Completion.N19n.PrimitiveInputs
public import SKConstants.Completion.N4c.Node
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology Matrix.Norms.L2Operator
namespace SKConstants.Completion.N19n
open GaussianProposal Blueprint Blueprint4 N19
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type} [MeasurableSpace Ω]

theorem coarseContinuity_inclusion_of_primitiveBounds
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (p : Parameters)
    (hf : FineExponents p) (hb : CoarseCommon p) (hag : p.a < p.grid)
    (CB CD u : ℝ) (hu : 0 < u)
    (hprim : ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ) (z : Outer n × Internal p n),
      z ∈ experimentCap p n CB CD n →
      ReplayPrimitiveBounds (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
        (coarseReplayAux p n hb.2.1.le (angleAux p n θ z.2))
        (coarseReplayAux p n hb.2.1.le (angleAux p n φ z.2))
        (coarseReplayMatrix p n (angleMatrix p n θ z.1 z.2))
        (coarseReplayMatrix p n (angleMatrix p n φ z.1 z.2))
        ((n : ℝ)^u*|θ-φ|) ((n : ℝ)^u)) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      {z | (hammingRadius p n : ℝ)/4 <
        magGap (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n (j+1)) z.1 z.2)
          (angleAux p n (gridAngle p n (j+1)) z.2))
        (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n j) z.1 z.2)
          (angleAux p n (gridAngle p n j) z.2))} ⊆
      (coarseStabilityGood W β hβ p n hb.2.1.le CB CD
        (gridAngle p n (j+1)) (gridAngle p n j))ᶜ := by
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hba : p.b/4 ≤ p.a := by linarith [hf.1, hb.2.1]
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  obtain ⟨k, hk, hfactor⟩ := coarse_factors_eventually_polynomial W β hβ p hf hb u hu.le
  filter_upwards [hprim, hfactor, grid_replay_estimate_eventually p ha.le hag u k hu.le hk.le,
    schedule_eventually p.a p.b hb.1 hba ha1] with n hp hfac hgrid hs j
  have hn : 0 < n := by omega
  have hN : 0 < rankCount p.a p.b n + queryCount p.a p.b n := by rw [rankCount_add]; omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hq : (queryCount p.a p.b n : ℝ) ≤ 8*(n : ℝ)^p.a :=
    (Nat.cast_le.mpr (show queryCount p.a p.b n ≤ stopIndex p.a p.b n by unfold queryCount; omega)).trans
      (stopIndex_le p.a p.b hb.1 hba n hn)
  have hsmall (j : Fin (queryCount p.a p.b n)) :
      growingQueryDuration (meshSize p.a n) (j.val+1) ≤ 1 := by
    have hd := (duration_bound p.a p.b hb.1 n hs.1 hs.2.1 (j.val+1) (by omega)).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith : p.b/4-p.a ≤ 0))
    exact_mod_cast hd
  intro z hz hgood
  have hP := hp (gridAngle p n (j+1)) (gridAngle p n j) z hgood.1
  have hG : ‖replayTargetGram W β hβ (meshSize p.a n) (rankCount p.a p.b n)
      (queryCount p.a p.b n) (Real.sqrt (rankCount p.a p.b n + queryCount p.a p.b n : ℕ))⁻¹
      (coarseReplayMatrix p n (angleMatrix p n (gridAngle p n (j+1)) z.1 z.2))
      (coarseReplayAux p n hb.2.1.le (angleAux p n (gridAngle p n (j+1)) z.2)) - 1‖ ≤ (3/4 : ℝ) := by
    have he := coarseReplay_targetGram_eq W β hβ p n hn hb.2.1.le
      (angleInput p n (gridAngle p n (j+1)) 0 z)
    simp only [angleInput] at he
    exact (congrArg (fun A => ‖A-1‖) he).le.trans hgood.2.1
  have hG' : ‖replayTargetGram W β hβ (meshSize p.a n) (rankCount p.a p.b n)
      (queryCount p.a p.b n) (Real.sqrt (rankCount p.a p.b n + queryCount p.a p.b n : ℕ))⁻¹
      (coarseReplayMatrix p n (angleMatrix p n (gridAngle p n j) z.1 z.2))
      (coarseReplayAux p n hb.2.1.le (angleAux p n (gridAngle p n j) z.2)) - 1‖ ≤ (3/4 : ℝ) := by
    have he := coarseReplay_targetGram_eq W β hβ p n hn hb.2.1.le
      (angleInput p n (gridAngle p n j) 0 z)
    simp only [angleInput] at he
    exact (congrArg (fun A => ‖A-1‖) he).le.trans hgood.2.2
  have hmag := actual_replayMag_gap_le W β hβ (meshSize p.a n)
    (paperGrowingQueryMeshSize_pos p.a n hn) _ _ hN _ _ _ _ _ _ (by positivity) (by positivity)
    (readoutTime p.a p.b n) hP.1 hP.2.1 hsmall hP.2.2.1 hP.2.2.2.1
    hP.2.2.2.2.1 hP.2.2.2.2.2.1 hP.2.2.2.2.2.2 hG hG'
  have hF0 : 0 ≤ actualReplayGapFactor W β (meshSize p.a n) (rankCount p.a p.b n)
      (queryCount p.a p.b n) ((n : ℝ)^u) := by
    unfold actualReplayGapFactor coupledScalarQueryGapFactor scalarQueryTargetGapFactor
      queryEndpointGapFactor queryDirectionGapFactor
    positivity
  have harith := hgrid _ hq _ _ hF0 (Real.exp_pos _).le hfac.1 hfac.2 j
  have hmag' : magGap
      (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n (j+1)) z.1 z.2)
        (angleAux p n (gridAngle p n (j+1)) z.2))
      (coarseMag W β hβ p n (angleMatrix p n (gridAngle p n j) z.1 z.2)
        (angleAux p n (gridAngle p n j) z.2)) ≤ 1/4 := by
    rw [coarseMag_gap_eq_replay W β hβ p n hb.2.1.le]
    exact hmag.trans (by simpa only [rankCount_add, readoutTime, scalarGrowingSourceHorizon] using harith)
  have hr : 1 ≤ hammingRadius p n := by
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
  have hrR : (1 : ℝ) ≤ hammingRadius p n := by exact_mod_cast hr
  exact (not_lt_of_ge (hmag'.trans (by linarith))) hz

theorem coarseContinuityCommonStatement_holds
    (hPrimitive : CoarsePrimitiveInputBoundsStatement) : CoarseContinuityCommonStatement := by
  intro p sseq hf hb hboundary hseq Ω _ W β hβ
  obtain ⟨-, -, hag, -, -, -, -, -, -, -, -, hD⟩ := hseq
  obtain ⟨CB, CD, hCB, hCD, hprob⟩ :=
    coarseContinuity_goodInputs_common_holds replayRowLaw_holds W
  obtain ⟨u, hu, hprim⟩ := hPrimitive p hf hb hD.le CB CD hCB hCD
  refine ⟨1/2, by norm_num, ?_⟩
  filter_upwards [hprob p hf hb hD.le β hβ,
    coarseContinuity_inclusion_of_primitiveBounds W β hβ p hf hb hag CB CD u hu hprim]
    with n hn hinc j hj
  have hm := (measureReal_mono (h₂ := measure_ne_top (experimentLaw W p n) _) (hinc j)).trans
    (hn (gridAngle p n (j+1)) (gridAngle p n j))
  simpa only [div_eq_mul_inv, one_mul, neg_mul, mul_comm] using hm

end SKConstants.Completion.N19n
