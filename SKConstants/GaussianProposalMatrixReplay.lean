module

public import SKConstants.GaussianProposalPaperRevelation
import Mathlib.Tactic

set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SKConstants.GaussianProposal

@[expose] def frameProjection {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Eᵀ * E

theorem frame_mul_transpose {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i = j then 1 else 0) : E * Eᵀ = 1 := by
  ext i j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dot] using hE i j

theorem frameProjection_mul_transpose {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i = j then 1 else 0) :
    frameProjection E * Eᵀ = Eᵀ := by
  unfold frameProjection
  rw [Matrix.mul_assoc, frame_mul_transpose E hE, Matrix.mul_one]

theorem frame_mul_projection {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i = j then 1 else 0) :
    E * frameProjection E = E := by
  unfold frameProjection
  rw [← Matrix.mul_assoc, frame_mul_transpose E hE, Matrix.one_mul]

theorem paperFrame_projection {m n : ℕ} (E : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (v : Fin n → ℝ) : frameProjection (paperFrame E v) = frameProjection E := by
  let B := completionFrame (0 : Fin (m + 1)) (paperDirection E v)
  have hBB : Bᵀ * B = 1 := frame_mul_transpose Bᵀ
    (orthogonalBasis_columns B (completionFrame_orthogonal 0 (paperDirection E v)))
  change (B * E)ᵀ * (B * E) = Eᵀ * E
  rw [Matrix.transpose_mul]
  calc
    _ = Eᵀ * (Bᵀ * B) * E := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBB, Matrix.mul_one]

theorem tailRows_orthogonal {m n : ℕ} (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) :
    ∀ i j, dot (tailRows F i) (tailRows F j) = if i = j then 1 else 0 := by
  intro i j
  change dot (F i.succ) (F j.succ) = _
  simpa only [Fin.succ_inj] using hF i.succ j.succ

theorem frameProjection_query {m n : ℕ} (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) :
    frameProjection F *ᵥ F 0 = F 0 := by
  have hdecomp := tailProjection_eq_remove_first F
  change remainingProjection F = frameProjection F - Matrix.vecMulVec (F 0) (F 0) at hdecomp
  have h := remainingProjection_query F hF
  rw [hdecomp, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec] at h
  have hu : dot (F 0) (F 0) = 1 := by simpa using hF 0 0
  simp only [op_smul_eq_smul] at h
  change frameProjection F *ᵥ F 0 - dot (F 0) (F 0) • F 0 = 0 at h
  rw [hu, one_smul] at h
  exact sub_eq_zero.mp h

theorem remainingProjection_mul_frameProjection {m n : ℕ}
    (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) :
    remainingProjection F * frameProjection F = remainingProjection F := by
  have hdecomp : frameProjection F = remainingProjection F +
      Matrix.vecMulVec (F 0) (F 0) := by
    have h := tailProjection_eq_remove_first F
    change remainingProjection F = frameProjection F - Matrix.vecMulVec (F 0) (F 0) at h
    rw [h]
    abel
  rw [hdecomp, Matrix.mul_add, remainingProjection_idempotent F hF,
    Matrix.mul_vecMulVec, remainingProjection_query F hF,
    Matrix.zero_vecMulVec, add_zero]

theorem frameProjection_mul_remainingProjection {m n : ℕ}
    (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0) :
    frameProjection F * remainingProjection F = remainingProjection F := by
  have h := congrArg Matrix.transpose (remainingProjection_mul_frameProjection F hF)
  simpa only [Matrix.transpose_mul, frameProjection, remainingProjection,
    Matrix.transpose_mul, Matrix.transpose_transpose] using h

variable {Past : Type*} [MeasurableSpace Past]

theorem paperTensorProposal_projection_support (r n K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n K Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) K) :
    frameProjection s.2 * paperTensorProposal r n sigma target update K s z *
      frameProjection s.2 = paperTensorProposal r n sigma target update K s z := by
  rw [← paperTensorOutput_eq_tensor r n sigma target update K s z]
  unfold paperTensorOutput
  calc
    _ = (frameProjection s.2 * s.2ᵀ) *
        fillSymmetricMatrix (paperCausalUpper r n sigma target update K s z) *
        (s.2 * frameProjection s.2) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [frameProjection_mul_transpose s.2 horth,
      frame_mul_projection s.2 horth]

theorem physicalColumnTerm_remaining_compression {m n : ℕ} (sigma : ℝ)
    (F : Matrix (Fin (m + 1)) (Fin n) ℝ)
    (hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    remainingProjection F * physicalColumnTerm sigma m F z * remainingProjection F = 0 := by
  have hu : F 0 ᵥ* remainingProjection F = 0 := by
    rw [← Matrix.mulVec_transpose]
    simpa only [remainingProjection, Matrix.transpose_mul,
      Matrix.transpose_transpose] using remainingProjection_query F hF
  unfold physicalColumnTerm
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, remainingProjection_query F hF,
    hu, Matrix.zero_vecMulVec, Matrix.vecMulVec_zero, smul_zero, add_zero, Matrix.zero_mul]

theorem paperTensorProposal_remaining_compression (r n K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n (K + 1) Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) (K + 1)) :
    let F := paperFrame s.2 (target K s.1)
    remainingProjection F * paperTensorProposal r n sigma target update (K + 1) s z *
      remainingProjection F =
      paperTensorProposal r n sigma target update K (update K s.1 z.1, tailRows F) z.2 := by
  let F := paperFrame s.2 (target K s.1)
  have hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0 :=
    paperFrame_orthogonal s.2 (target K s.1) horth
  change remainingProjection F *
    (physicalColumnTerm sigma (r + K) F z.1 +
      paperTensorProposal r n sigma target update K (update K s.1 z.1, tailRows F) z.2) *
    remainingProjection F = _
  rw [Matrix.mul_add, Matrix.add_mul]
  have hc := physicalColumnTerm_remaining_compression sigma F hF z.1
  change remainingProjection F * physicalColumnTerm sigma (r + K) F z.1 *
    remainingProjection F = 0 at hc
  rw [hc, zero_add]
  exact paperTensorProposal_projection_support r n K sigma target update
    (update K s.1 z.1, tailRows F) (tailRows_orthogonal F hF) z.2

theorem matrix_query_completed_endpoint_of_compression (r n K : ℕ)
    (N : ℝ) (hN : 0 < N)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n (K + 1) Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) (K + 1)) (W : Matrix (Fin n) (Fin n) ℝ)
    (hcompression : frameProjection s.2 * W * frameProjection s.2 =
      paperTensorProposal r n (skSigma N) target update (K + 1) s z) :
    let F := paperFrame s.2 (target K s.1)
    remainingProjection F *ᵥ (W *ᵥ normalizedQuery N (F 0)) +
      (1 - remainingProjection F) *ᵥ (fun i => z.1 (.inl i)) =
      fun i => z.1 (.inl i) := by
  let F := paperFrame s.2 (target K s.1)
  let P := frameProjection s.2
  let u := normalizedQuery N (F 0)
  have hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0 :=
    paperFrame_orthogonal s.2 (target K s.1) horth
  have hleft : remainingProjection F * P = remainingProjection F := by
    change remainingProjection F * frameProjection s.2 = _
    rw [← paperFrame_projection s.2 (target K s.1)]
    exact remainingProjection_mul_frameProjection F hF
  have hunit : P *ᵥ u = u := by
    change frameProjection s.2 *ᵥ (Real.sqrt N • F 0) = _
    rw [← paperFrame_projection s.2 (target K s.1),
      Matrix.mulVec_smul, frameProjection_query F hF]
    rfl
  have heq : remainingProjection F *ᵥ (W *ᵥ u) =
      remainingProjection F *ᵥ
        (paperTensorProposal r n (skSigma N) target update (K + 1) s z *ᵥ u) := by
    calc
      _ = (remainingProjection F * P) *ᵥ (W *ᵥ (P *ᵥ u)) := by rw [hleft, hunit]
      _ = remainingProjection F *ᵥ ((P * W * P) *ᵥ u) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by rw [hcompression]
  change remainingProjection F *ᵥ (W *ᵥ u) + _ = _
  rw [heq]
  exact paperTensorProposal_SK_completed_endpoint r n K N hN target update s horth z

theorem matrix_remaining_compression_of_compression (r n K : ℕ) (sigma : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (s : PaperState r n (K + 1) Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) (K + 1)) (W : Matrix (Fin n) (Fin n) ℝ)
    (hcompression : frameProjection s.2 * W * frameProjection s.2 =
      paperTensorProposal r n sigma target update (K + 1) s z) :
    let F := paperFrame s.2 (target K s.1)
    remainingProjection F * W * remainingProjection F =
      paperTensorProposal r n sigma target update K (update K s.1 z.1, tailRows F) z.2 := by
  let F := paperFrame s.2 (target K s.1)
  let P := frameProjection s.2
  have hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0 :=
    paperFrame_orthogonal s.2 (target K s.1) horth
  have hleft : remainingProjection F * P = remainingProjection F := by
    change remainingProjection F * frameProjection s.2 = _
    rw [← paperFrame_projection s.2 (target K s.1)]
    exact remainingProjection_mul_frameProjection F hF
  have hright : P * remainingProjection F = remainingProjection F := by
    change frameProjection s.2 * remainingProjection F = _
    rw [← paperFrame_projection s.2 (target K s.1)]
    exact frameProjection_mul_remainingProjection F hF
  calc
    _ = (remainingProjection F * P) * W * (P * remainingProjection F) := by
      rw [hleft, hright]
    _ = remainingProjection F * (P * W * P) * remainingProjection F := by
      simp only [Matrix.mul_assoc]
    _ = remainingProjection F *
        paperTensorProposal r n sigma target update (K + 1) s z * remainingProjection F := by
      rw [hcompression]
    _ = _ := paperTensorProposal_remaining_compression r n K sigma target update s horth z

@[expose] def paperQueriedNoise {m n : ℕ} (N : ℝ)
    (F : Matrix (Fin (m + 1)) (Fin n) ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) : EuclideanSpace ℝ (Fin n ⊕ Unit) :=
  WithLp.toLp 2 (Sum.elim
    (remainingProjection F *ᵥ (W *ᵥ normalizedQuery N (F 0)) +
      (1 - remainingProjection F) *ᵥ (fun i => z (.inl i)))
    (fun _ => z (.inr ())))

@[expose] def paperMatrixQueryRun (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K →
      Matrix (Fin n) (Fin n) ℝ → Past
  | 0, s, _, _ => s.1
  | K + 1, s, z, W =>
      let F := paperFrame s.2 (target K s.1)
      paperMatrixQueryRun r n N target update K
        (update K s.1 (paperQueriedNoise N F W z.1), tailRows F) z.2 W

theorem paperMatrixQueryRun_eq_generated (r n : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i = j then 1 else 0)
    (z : StoppedNoise (Fin n) K) (W : Matrix (Fin n) (Fin n) ℝ)
    (hcompression : frameProjection s.2 * W * frameProjection s.2 =
      paperTensorProposal r n (skSigma N) target update K s z) :
    paperMatrixQueryRun r n N target update K s z W =
      proposalTerminalPast update K s.1 z := by
  induction K generalizing W with
  | zero => rfl
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    have hF : ∀ i j, dot (F i) (F j) = if i = j then 1 else 0 :=
      paperFrame_orthogonal s.2 (target K s.1) horth
    have he : paperQueriedNoise N F W z.1 = z.1 := by
      ext i
      cases i with
      | inl i =>
          exact congrFun (matrix_query_completed_endpoint_of_compression
            r n K N hN target update s horth z W hcompression) i
      | inr i => cases i; rfl
    change paperMatrixQueryRun r n N target update K
      (update K s.1 (paperQueriedNoise N F W z.1), tailRows F) z.2 W =
        proposalTerminalPast update K (update K s.1 z.1) z.2
    rw [he]
    apply ih (update K s.1 z.1, tailRows F) (tailRows_orthogonal F hF) z.2 W
    exact matrix_remaining_compression_of_compression r n K (skSigma N)
      target update s horth z W hcompression

theorem actualPaperProposal_matrix_query_coupling (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (k : ℕ) → Past → Fin (r + K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r + K)) K) :
    paperMatrixQueryRun r (r + K) N target update K (a, 1) z
      (actualPaperProposal r K (skSigma N) target update a z) =
      proposalTerminalPast update K a z := by
  have horth : ∀ i j : Fin (r + K),
      dot ((1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ) i)
        ((1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ) j) =
          if i = j then 1 else 0 := by
    intro i j
    have hId : (1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ) = canonicalBasis := by
      ext i j
      exact Matrix.one_apply
    rw [hId]
    exact canonicalBasis_orthogonal i j
  apply paperMatrixQueryRun_eq_generated r (r + K) N hN target update K (a, 1) horth z
  change frameProjection (1 : Matrix (Fin (r + K)) (Fin (r + K)) ℝ) *
    actualPaperProposal r K (skSigma N) target update a z * frameProjection 1 = _
  simp only [frameProjection, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rfl

end SKConstants.GaussianProposal
