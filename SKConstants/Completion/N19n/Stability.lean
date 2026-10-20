module

public import SKConstants.Completion.N19n.ScaleBounds
public import SKConstants.Completion.N19n.CoarseReplay
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal Topology Matrix.Norms.L2Operator
namespace SKConstants.Completion.N19n
open GaussianProposal Blueprint N19
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type} [MeasurableSpace Ω]

def actualReplayGapFactor (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (r q : ℕ) (A : ℝ) : ℝ :=
  coupledScalarQueryGapFactor (r+q) q
    (scalarQueryTargetGapFactor (actualParisiFullScalarDrift β) (scalarGrowingSourceHorizon δ q)
      2 (Real.sqrt ((δ : ℝ) * actualParisiFullSusceptibilitySquareExpected W β
        (scalarGrowingSourceHorizon δ q)))) A

theorem actual_replayMag_gap_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) (hN : 0 < r+q)
    (a b : ReplayAux δ r q) (M M' : Matrix (Fin (r+q)) (Fin (r+q)) ℝ)
    (η A : ℝ) (hη : 0 ≤ η) (hA : 0 ≤ A) (v : ℝ≥0)
    (hD : ∀ i, ‖a.2.2 i - b.2.2 i‖ ≤ η)
    (hInitial : scalarMeshPathGap (replayStart δ r q a) (replayStart δ r q b) ≤ η)
    (hsmall : ∀ j : Fin q, growingQueryDuration δ (j.val+1) ≤ 1)
    (hbridge : ∀ j : Fin q, (∑ i, ‖a.1.2 (j.val+1) i - b.1.2 (j.val+1) i‖) ≤ η)
    (hM : ‖M-M'‖ ≤ η) (hM' : ‖M'‖ ≤ A)
    (hz : ∀ j : Fin q, ‖WithLp.toLp 2 (fun i => paperNoiseTrace (r+q) q
      (paperCompletionReplayNoise (r+q) q a.2.1) j (.inl i))‖ ≤ A)
    (hzw : ∀ j : Fin q, ‖WithLp.toLp 2 (fun i =>
      paperNoiseTrace (r+q) q (paperCompletionReplayNoise (r+q) q a.2.1) j (.inl i) -
      paperNoiseTrace (r+q) q (paperCompletionReplayNoise (r+q) q b.2.1) j (.inl i))‖ ≤ η)
    (hGram : ‖replayTargetGram W β hβ δ r q (Real.sqrt (r+q : ℕ))⁻¹ M a - 1‖ ≤ (3/4 : ℝ))
    (hGram' : ‖replayTargetGram W β hβ δ r q (Real.sqrt (r+q : ℕ))⁻¹ M' b - 1‖ ≤ (3/4 : ℝ)) :
    magGap (replayMag W β hβ δ r q v M a) (replayMag W β hβ δ r q v M' b) ≤
      (r+q : ℕ) * (4 * (2 * η * (actualReplayGapFactor W β δ r q A)^q + η) *
        Real.exp ((actualParisiFullScalarDrift β).rate * (scalarGrowingSourceHorizon δ q)))^2 := by
  have hc : 0 < (Real.sqrt (r+q : ℕ))⁻¹ := by positivity
  have hcN : (Real.sqrt (r+q : ℕ))⁻¹ * Real.sqrt (r+q : ℕ) ≤ 1 := by
    rw [inv_mul_cancel₀ (by positivity : Real.sqrt (r+q : ℕ) ≠ 0)]
  have hp := actual_replayPathGap_le W β hβ δ r q a b M M'
    (Real.sqrt (r+q : ℕ))⁻¹ η 2 A _ hc hη (by norm_num) hA
    (growing_incrementScale_lower_pos W β hβ δ hδ q) hcN hD hInitial
    (negativeRho_pathBound_le_two W β hβ _) (sigma_pathBound_le_two W β hβ _)
    (fun j => ⟨growingQueryDuration_pos δ hδ _, hsmall j⟩)
    (growing_incrementScale_lower W β hβ δ hδ q) hbridge hM hM' hz hzw hGram hGram'
  simpa only [show (2 : ℝ) * 2 = 4 from by norm_num] using replayMag_gap_of_pathGap W β hβ δ r q v a b M M' η 2
    (2 * η * (actualReplayGapFactor W β δ r q A)^q) (by norm_num) hD
    (negativeRho_pathBound_le_two W β hβ _) (sigma_pathBound_le_two W β hβ _) hp

end SKConstants.Completion.N19n
