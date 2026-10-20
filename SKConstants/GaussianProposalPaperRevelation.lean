module

public import SKConstants.GaussianProposalPaperCausal
import Mathlib.Tactic

set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SKConstants.GaussianProposal

variable {m n : ℕ}

@[expose] def remainingProjection (F : Matrix (Fin (m + 1)) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (tailRows F)ᵀ * tailRows F

theorem tailRows_mulVec_query (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) :
    tailRows F *ᵥ F 0 = 0 := by
  ext i
  change dot (F i.succ) (F 0) = 0
  simpa only [Fin.succ_ne_zero, ↓reduceIte] using hF i.succ 0

theorem remainingProjection_query (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) :
    remainingProjection F *ᵥ F 0 = 0 := by
  unfold remainingProjection
  rw [← Matrix.mulVec_mulVec, tailRows_mulVec_query F hF, Matrix.mulVec_zero]

theorem remainingProjection_idempotent (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) :
    remainingProjection F * remainingProjection F = remainingProjection F := by
  have htail : tailRows F * (tailRows F)ᵀ = 1 := by
    ext i j
    change dot (F i.succ) (F j.succ) = if i = j then 1 else 0
    simpa only [Fin.succ_inj] using hF i.succ j.succ
  unfold remainingProjection
  calc
    _ = (tailRows F)ᵀ * (tailRows F * (tailRows F)ᵀ) * tailRows F := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [htail, Matrix.mul_one]

theorem query_dot_remaining (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) (g : Fin n → ℝ) :
    dot (remainingProjection F *ᵥ g) (F 0) = 0 := by
  have hq := tailRows_mulVec_query F hF
  change (((tailRows F)ᵀ * tailRows F) *ᵥ g) ⬝ᵥ (F 0) = 0
  rw [← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, hq, zero_dotProduct]

theorem physicalColumnTerm_mulVec_query (sigma : ℝ)
    (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    physicalColumnTerm sigma m F z *ᵥ F 0 =
      (2 * sigma * z (.inr ())) • F 0 +
        (Real.sqrt 2 * sigma) • (remainingProjection F *ᵥ (fun i => z (.inl i))) := by
  let f : Fin n → ℝ := (Real.sqrt 2 * sigma) •
    (remainingProjection F *ᵥ (fun i => z (.inl i)))
  have hunit : dot (F 0) (F 0) = 1 := by simpa using hF 0 0
  have hoff : dot f (F 0) = 0 := by
    change ((Real.sqrt 2 * sigma) • (remainingProjection F *ᵥ _)) ⬝ᵥ F 0 = 0
    rw [smul_dotProduct]
    change (Real.sqrt 2 * sigma) • dot (remainingProjection F *ᵥ (fun i => z (.inl i))) (F 0) = 0
    rw [query_dot_remaining F hF, smul_zero]
  change ((2 * sigma * z (.inr ())) • Matrix.vecMulVec (F 0) (F 0) +
    Matrix.vecMulVec (F 0) f + Matrix.vecMulVec f (F 0)) *ᵥ F 0 = _
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  change (2 * sigma * z (.inr ())) • (dot (F 0) (F 0) • F 0) +
    dot f (F 0) • F 0 + dot (F 0) (F 0) • f = _
  rw [hunit, hoff]
  simp only [one_smul, zero_smul, add_zero]
  rfl

variable {Past : Type*} [MeasurableSpace Past]

theorem paperTensorProposal_mulVec_query (r n K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n (K + 1) Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) (K + 1)) :
    let F := paperFrame s.2 (target K s.1)
    paperTensorProposal r n sigma target update (K + 1) s z *ᵥ F 0 =
      (2 * sigma * z.1 (.inr ())) • F 0 +
        (Real.sqrt 2 * sigma) • (remainingProjection F *ᵥ (fun i => z.1 (.inl i))) := by
  let F := paperFrame s.2 (target K s.1)
  have hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0 :=
    paperFrame_orthogonal s.2 (target K s.1) horth
  have hfuture : paperTensorProposal r n sigma target update K
      (update K s.1 z.1, tailRows F) z.2 *ᵥ F 0 = 0 := by
    rw [← paperTensorOutput_eq_tensor r n sigma target update K
      (update K s.1 z.1, tailRows F) z.2]
    unfold paperTensorOutput
    rw [← Matrix.mulVec_mulVec, tailRows_mulVec_query F hF, Matrix.mulVec_zero]
  change (physicalColumnTerm sigma (r + K) F z.1 +
    paperTensorProposal r n sigma target update K (update K s.1 z.1, tailRows F) z.2) *ᵥ F 0 = _
  rw [Matrix.add_mulVec]
  have hc := physicalColumnTerm_mulVec_query sigma F hF z.1
  change physicalColumnTerm sigma (r + K) F z.1 *ᵥ F 0 = _ at hc
  rw [hc, hfuture, add_zero]

theorem paperTensorProposal_SK_query_endpoint (r n K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n (K + 1) Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) (K + 1)) :
    let F := paperFrame s.2 (target K s.1)
    remainingProjection F *ᵥ
      (paperTensorProposal r n (skSigma N) target update (K + 1) s z *ᵥ
        normalizedQuery N (F 0)) =
      remainingProjection F *ᵥ (fun i => z.1 (.inl i)) := by
  let F := paperFrame s.2 (target K s.1)
  have hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0 :=
    paperFrame_orthogonal s.2 (target K s.1) horth
  have hs : Real.sqrt N * (Real.sqrt 2 * skSigma N) = 1 := by
    rw [skSigma_offScale N hN]
    calc
      _ = N⁻¹ * Real.sqrt N ^ 2 := by ring
      _ = 1 := by rw [Real.sq_sqrt (le_of_lt hN), inv_mul_cancel₀ (ne_of_gt hN)]
  change remainingProjection F *ᵥ
    (paperTensorProposal r n (skSigma N) target update (K + 1) s z *ᵥ
      (Real.sqrt N • F 0)) = _
  rw [Matrix.mulVec_smul, paperTensorProposal_mulVec_query r n K (skSigma N)
    target update s horth z]
  change remainingProjection F *ᵥ (Real.sqrt N •
    ((2 * skSigma N * z.1 (.inr ())) • F 0 +
      (Real.sqrt 2 * skSigma N) • (remainingProjection F *ᵥ (fun i => z.1 (.inl i))))) = _
  rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
    remainingProjection_query F hF, smul_zero, zero_add, Matrix.mulVec_smul]
  rw [Matrix.mulVec_mulVec, remainingProjection_idempotent F hF, smul_smul, hs, one_smul]

theorem paperTensorProposal_SK_completed_endpoint (r n K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n (K + 1) Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) (K + 1)) :
    let F := paperFrame s.2 (target K s.1)
    remainingProjection F *ᵥ
      (paperTensorProposal r n (skSigma N) target update (K + 1) s z *ᵥ
        normalizedQuery N (F 0)) +
      (1 - remainingProjection F) *ᵥ (fun i => z.1 (.inl i)) =
      fun i => z.1 (.inl i) := by
  dsimp only
  rw [paperTensorProposal_SK_query_endpoint r n K N hN target update s horth z]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

end SKConstants.GaussianProposal
