module

public import SKConstants.GaussianProposalColumnAssembly
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

theorem fillSymmetricMatrix_isSymm {ι : Type*} [LinearOrder ι]
    (q : UpperPair ι → ℝ) : (fillSymmetricMatrix q).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, fillSymmetricMatrix, sortedPair]
  congr 1
  apply Subtype.ext
  simp [min_comm, max_comm]

theorem fill_matrixUpper_of_isSymm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) : fillSymmetricMatrix (matrixUpper M) = M := by
  ext i j
  by_cases hij : i ≤ j
  · simp [fillSymmetricMatrix, matrixUpper, sortedPair,
      min_eq_left hij, max_eq_right hij]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simpa [fillSymmetricMatrix, matrixUpper, sortedPair,
      min_eq_right hji, max_eq_left hji] using hM.apply i j

theorem basisAssembly_isSymm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (q : UpperPair (Fin n) → ℝ) : (basisAssembly B q).IsSymm := by
  have hq := fillSymmetricMatrix_isSymm q
  unfold basisAssembly Matrix.IsSymm at *
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hq]
  noncomm_ring

theorem compressedMatrix_eq_conjugation {Ambient : Type} [Fintype Ambient]
    [DecidableEq Ambient] {n : ℕ} (sigma : ℝ)
    (E : Matrix (Fin n) Ambient ℝ) (z : EuclideanSpace ℝ (Ambient × Ambient)) :
    fillSymmetricMatrix (fun p => compressedEntry sigma E p z) =
      E * goeMatrix sigma z * Eᵀ := by
  have hentry (i j : Fin n) :
      fillSymmetricMatrix (fun p => compressedEntry sigma E p z) i j =
        goeBilinear sigma (E i) (E j) z := by
    by_cases hij : i ≤ j
    · simp [fillSymmetricMatrix, sortedPair, compressedEntry,
        min_eq_left hij, max_eq_right hij]
    · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
      simp only [fillSymmetricMatrix, sortedPair, min_eq_right hji, max_eq_left hji,
        compressedEntry]
      exact goeBilinear_symmetric sigma (E j) (E i) z
  ext i j
  rw [hentry, goeBilinear_eq_matrix, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_assoc]

variable {Ambient : Type} [Fintype Ambient] [DecidableEq Ambient]
variable {Past : Type*} [MeasurableSpace Past]

@[expose] def physicalColumnTerm (sigma : ℝ) (n : ℕ)
    (frame : Matrix (Fin (n + 1)) Ambient ℝ)
    (z : EuclideanSpace ℝ (Ambient ⊕ Unit)) : Matrix Ambient Ambient ℝ :=
  let f := (Real.sqrt 2 * sigma) • (((tailRows frame)ᵀ * tailRows frame) *ᵥ
    (fun i => z (.inl i)))
  (2 * sigma * z (.inr ())) • Matrix.vecMulVec (frame 0) (frame 0) +
    Matrix.vecMulVec (frame 0) f + Matrix.vecMulVec f (frame 0)

@[expose] def physicalTensorProposal (r : ℕ) (sigma : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (K : ℕ) → Past → StoppedNoise Ambient K → Matrix Ambient Ambient ℝ
  | 0, a, z => (embedding 0 a)ᵀ * embedding 0 a * goeMatrix sigma z *
      ((embedding 0 a)ᵀ * embedding 0 a)
  | K + 1, a, z => physicalColumnTerm sigma (r + K) (frame K a) z.1 +
      physicalTensorProposal r sigma embedding frame update K (update K a z.1) z.2

@[expose] def physicalStoppedOutput (r : ℕ) (sigma : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) : Matrix Ambient Ambient ℝ :=
  (embedding K a)ᵀ *
    stoppedCausalGOE r sigma (embedding 0) direction frame update K a z * embedding K a

theorem physicalStoppedOutput_step (r : ℕ) (sigma : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient (K + 1))
    (hframe : frame K a = completionFrame 0 (direction K a) * embedding (K + 1) a)
    (hnext : embedding K (update K a z.1) = tailRows (frame K a)) :
    physicalStoppedOutput r sigma embedding direction frame update (K + 1) a z =
      physicalColumnTerm sigma (r + K) (frame K a) z.1 +
      physicalStoppedOutput r sigma embedding direction frame update K (update K a z.1) z.2 := by
  let B := completionFrame (0 : Fin (r + K + 1)) (direction K a)
  let c := ambientColumn sigma (r + K) (frame K a) z.1
  let q := stoppedCausalUpper r sigma (embedding 0) direction frame update K
    (update K a z.1) z.2
  let E := embedding (K + 1) a
  have hF : frame K a = B * E := hframe
  change Eᵀ * fillSymmetricMatrix (matrixUpper (basisAssembly B (joinUpper (r + K) (c, q)))) * E = _
  rw [fill_matrixUpper_of_isSymm _ (basisAssembly_isSymm B _)]
  have hconj : Eᵀ * basisAssembly B (joinUpper (r + K) (c, q)) * E =
      (frame K a)ᵀ * borderMatrix (r + K) c (fillSymmetricMatrix q) * frame K a := by
    rw [hF, Matrix.transpose_mul]
    unfold basisAssembly
    rw [fillJoin_border]
    simp only [Matrix.mul_assoc]
  rw [hconj, border_conjugation_decomposition]
  change c 0 • Matrix.vecMulVec (frame K a 0) (frame K a 0) +
    Matrix.vecMulVec (frame K a 0) (columnOffVector (frame K a) c) +
    Matrix.vecMulVec (columnOffVector (frame K a) c) (frame K a 0) +
    (tailRows (frame K a))ᵀ * fillSymmetricMatrix q * tailRows (frame K a) = _
  have hdiag : c 0 = 2 * sigma * z.1 (.inr ()) := ambientColumn_zero sigma (r + K) _ _
  have hoff := ambientColumn_offVector sigma (r + K) (frame K a) z.1
  change columnOffVector (frame K a) c = _ at hoff
  rw [hdiag, hoff]
  unfold physicalColumnTerm physicalStoppedOutput stoppedCausalGOE
  rw [hnext]

theorem physicalStoppedOutput_eq_tensor (r : ℕ) (sigma : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (hframe : ∀ k a, frame k a = completionFrame 0 (direction k a) * embedding (k + 1) a)
    (hnext : ∀ k a z, embedding k (update k a z) = tailRows (frame k a))
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) :
    physicalStoppedOutput r sigma embedding direction frame update K a z =
      physicalTensorProposal r sigma embedding frame update K a z := by
  induction K generalizing a with
  | zero =>
    let E : Matrix (Fin r) Ambient ℝ := embedding 0 a
    change Eᵀ * fillSymmetricMatrix (fun p => compressedEntry sigma (fun i j => E i j) p z) * E =
      Eᵀ * E * goeMatrix sigma z * (Eᵀ * E)
    have hc := compressedMatrix_eq_conjugation sigma E z
    change fillSymmetricMatrix (fun p => compressedEntry sigma (fun i j => E i j) p z) =
      E * goeMatrix sigma z * Eᵀ at hc
    rw [hc]
    simp only [Matrix.mul_assoc]
  | succ K ih =>
    rw [physicalStoppedOutput_step r sigma embedding direction frame update K a z
      (hframe K a) (hnext K a z.1)]
    rw [ih]
    rfl

theorem physicalTensorProposal_law (r K : ℕ) (sigma : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) (Fin (r + K)) ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) (Fin (r + K)) ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (hembedding : ∀ k i j, Measurable (fun a => embedding k a i j))
    (hdirection : ∀ k j, Measurable (fun a => direction k a j))
    (hmeasframe : ∀ k j i, Measurable (fun a => frame k a j i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (hresorth : ∀ a i j,
      dot (embedding 0 a i) (embedding 0 a j) = if i = j then 1 else 0)
    (horth : ∀ k, k < K → ∀ a i j,
      dot (frame k a i) (frame k a j) = if i = j then 1 else 0)
    (hinitorth : ∀ a i j,
      dot (embedding K a i) (embedding K a j) = if i = j then 1 else 0)
    (hframe : ∀ k a, frame k a = completionFrame 0 (direction k a) * embedding (k + 1) a)
    (hnext : ∀ k a z, embedding k (update k a z) = tailRows (frame k a))
    (a : Past) :
    (stoppedNoiseLaw (Fin (r + K)) K).map
      (physicalTensorProposal r sigma embedding frame update K a) =
      (primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix sigma) := by
  have hfn : physicalTensorProposal r sigma embedding frame update K a =
      fun z => basisAssembly (embedding K a)
        (stoppedCausalUpper r sigma (embedding 0) direction frame update K a z) := by
    funext z
    exact (physicalStoppedOutput_eq_tensor r sigma embedding direction frame update
      hframe hnext K a z).symm
  have hsource : Measurable
      (stoppedCausalUpper r sigma (embedding 0) direction frame update K a) :=
    (stoppedCausalUpper_measurable r sigma (embedding 0) direction frame update
      (hembedding 0) hdirection hmeasframe hupdate K).comp
      (measurable_const.prodMk measurable_id)
  rw [hfn]
  calc
    _ = ((stoppedNoiseLaw (Fin (r + K)) K).map
        (stoppedCausalUpper r sigma (embedding 0) direction frame update K a)).map
          (basisAssembly (embedding K a)) :=
      (Measure.map_map (basisAssembly_measurable (embedding K a)) hsource).symm
    _ = (gaussianUpperLaw sigma (Fin (r + K))).map (basisAssembly (embedding K a)) := by
      rw [stoppedCausalUpper_law r sigma (embedding 0) direction frame update
        (hembedding 0) hdirection hmeasframe hupdate hresorth K horth a]
    _ = _ := basisAssembly_law sigma (embedding K a) (hinitorth a)

theorem physicalTensorProposal_joint_law
    (μ : Measure Past) [SFinite μ] (r K : ℕ) (sigma : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) (Fin (r + K)) ℝ)
    (direction : (k : ℕ) → Past → Fin (r + k + 1) → ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) (Fin (r + K)) ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r + K) ⊕ Unit) → Past)
    (hembedding : ∀ k i j, Measurable (fun a => embedding k a i j))
    (hdirection : ∀ k j, Measurable (fun a => direction k a j))
    (hmeasframe : ∀ k j i, Measurable (fun a => frame k a j i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (hresorth : ∀ a i j,
      dot (embedding 0 a i) (embedding 0 a j) = if i = j then 1 else 0)
    (horth : ∀ k, k < K → ∀ a i j,
      dot (frame k a i) (frame k a j) = if i = j then 1 else 0)
    (hinitorth : ∀ a i j,
      dot (embedding K a i) (embedding K a j) = if i = j then 1 else 0)
    (hframe : ∀ k a, frame k a = completionFrame 0 (direction k a) * embedding (k + 1) a)
    (hnext : ∀ k a z, embedding k (update k a z) = tailRows (frame k a)) :
    (μ.prod (stoppedNoiseLaw (Fin (r + K)) K)).map
      (fun x => (x.1, physicalTensorProposal r sigma embedding frame update K x.1 x.2)) =
      μ.prod ((primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix sigma)) := by
  have hsource := stoppedCausalUpper_measurable r sigma (embedding 0) direction frame update
    (hembedding 0) hdirection hmeasframe hupdate K
  have hphysical := (adaptiveAssembly_measurable (embedding K) (hembedding K)).comp
    (measurable_fst.prodMk hsource)
  have htensor : Measurable (Function.uncurry
      (physicalTensorProposal r sigma embedding frame update K)) := by
    convert hphysical using 1
    funext x
    exact (physicalStoppedOutput_eq_tensor r sigma embedding direction frame update
      hframe hnext K x.1 x.2).symm
  exact adaptiveStep_joint_law htensor
    (physicalTensorProposal_law r K sigma embedding direction frame update
      hembedding hdirection hmeasframe hupdate hresorth horth hinitorth hframe hnext)

end SKConstants.GaussianProposal
