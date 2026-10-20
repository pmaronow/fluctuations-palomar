module

public import SKConstants.GaussianProposalPhysicalIdentification
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

@[expose] def skSigma (N : ℝ) : ℝ := 1 / Real.sqrt (2 * N)

theorem skSigma_offScale (N : ℝ) (hN : 0 < N) :
    Real.sqrt 2 * skSigma N = N⁻¹ * Real.sqrt N := by
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsN : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  unfold skSigma
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  nlinarith [Real.sq_sqrt (le_of_lt hN)]

theorem skSigma_offVariance (N : ℝ) (hN : 0 < N) :
    2 * skSigma N ^ 2 = N⁻¹ := by
  have hs : Real.sqrt (2 * N) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos (by norm_num) hN))
  have hsq : Real.sqrt (2 * N) ^ 2 = 2 * N :=
    Real.sq_sqrt (le_of_lt (mul_pos (by norm_num) hN))
  unfold skSigma
  field_simp
  nlinarith

theorem skSigma_diagonalVariance (N : ℝ) (hN : 0 < N) :
    4 * skSigma N ^ 2 = 2 * N⁻¹ := by
  nlinarith [skSigma_offVariance N hN]

@[expose] def normalizedQuery {Ambient : Type*} (N : ℝ) (u : Ambient → ℝ) : Ambient → ℝ :=
  Real.sqrt N • u

@[expose] def normalizedColumnMatrix {Ambient : Type*}
    (N : ℝ) (u f : Ambient → ℝ) (d : ℝ) : Matrix Ambient Ambient ℝ :=
  N⁻¹ • (Matrix.vecMulVec u f + Matrix.vecMulVec f u) +
    (N⁻¹ * d) • Matrix.vecMulVec u u

theorem normalizedQuery_normSq {Ambient : Type*} [Fintype Ambient]
    (N : ℝ) (hN : 0 ≤ N) (u : Ambient → ℝ) (hu : dot u u = 1) :
    dot (normalizedQuery N u) (normalizedQuery N u) = N := by
  have hterm (i : Ambient) : (Real.sqrt N * u i) * (Real.sqrt N * u i) =
      Real.sqrt N ^ 2 * (u i * u i) := by ring
  simp only [normalizedQuery, dot, Pi.smul_apply, smul_eq_mul]
  simp_rw [hterm, ← Finset.mul_sum]
  change Real.sqrt N ^ 2 * dot u u = N
  rw [hu, mul_one, Real.sq_sqrt hN]

theorem physicalColumnTerm_SK_normalized {Ambient : Type} [Fintype Ambient]
    [DecidableEq Ambient] (N : ℝ) (hN : 0 < N) (n : ℕ)
    (frame : Matrix (Fin (n + 1)) Ambient ℝ)
    (z : EuclideanSpace ℝ (Ambient ⊕ Unit)) :
    physicalColumnTerm (skSigma N) n frame z =
      normalizedColumnMatrix N (normalizedQuery N (frame 0))
        (((tailRows frame)ᵀ * tailRows frame) *ᵥ (fun i => z (.inl i)))
        (2 * skSigma N * z (.inr ())) := by
  have hs : N⁻¹ * Real.sqrt N ^ 2 = 1 := by
    rw [Real.sq_sqrt (le_of_lt hN)]
    exact inv_mul_cancel₀ (ne_of_gt hN)
  ext i j
  simp only [physicalColumnTerm, normalizedColumnMatrix, normalizedQuery,
    Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [skSigma_offScale N hN]
  have hdiag (a b d : ℝ) : N⁻¹ * d * (Real.sqrt N * a * (Real.sqrt N * b)) = d * (a * b) := by
    calc
      _ = (N⁻¹ * Real.sqrt N ^ 2) * (d * a * b) := by ring
      _ = _ := by rw [hs]; ring
  rw [hdiag]
  ring

@[expose] def normalizedTensorProposal {Ambient : Type} [Fintype Ambient] [DecidableEq Ambient]
    {Past : Type*} [MeasurableSpace Past] (r : ℕ) (N : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (K : ℕ) → Past → StoppedNoise Ambient K → Matrix Ambient Ambient ℝ
  | 0, a, z => (embedding 0 a)ᵀ * embedding 0 a * goeMatrix (skSigma N) z *
      ((embedding 0 a)ᵀ * embedding 0 a)
  | K + 1, a, z => normalizedColumnMatrix N (normalizedQuery N (frame K a 0))
      (((tailRows (frame K a))ᵀ * tailRows (frame K a)) *ᵥ (fun i => z.1 (.inl i)))
      (2 * skSigma N * z.1 (.inr ())) +
      normalizedTensorProposal r N embedding frame update K (update K a z.1) z.2

theorem physicalTensorProposal_SK_normalized {Ambient : Type} [Fintype Ambient]
    [DecidableEq Ambient] {Past : Type*} [MeasurableSpace Past]
    (r : ℕ) (N : ℝ) (hN : 0 < N)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) :
    physicalTensorProposal r (skSigma N) embedding frame update K a z =
      normalizedTensorProposal r N embedding frame update K a z := by
  induction K generalizing a with
  | zero => rfl
  | succ K ih =>
    change physicalColumnTerm (skSigma N) (r + K) (frame K a) z.1 +
      physicalTensorProposal r (skSigma N) embedding frame update K (update K a z.1) z.2 = _
    rw [physicalColumnTerm_SK_normalized N hN, ih]
    rfl

@[expose] def proposalTerminalPast {Ambient : Type} {Past : Type*}
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (K : ℕ) → Past → StoppedNoise Ambient K → Past
  | 0, a, _ => a
  | K + 1, a, z => proposalTerminalPast update K (update K a z.1) z.2

@[expose] def proposalResidualPrimitive {Ambient : Type} :
    (K : ℕ) → StoppedNoise Ambient K → EuclideanSpace ℝ (Ambient × Ambient)
  | 0, z => z
  | K + 1, z => proposalResidualPrimitive K z.2

@[expose] def proposalQueryColumns {Ambient : Type} {Past : Type*}
    (r : ℕ) (N : ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (K : ℕ) → Past → StoppedNoise Ambient K → Fin K → Ambient → ℝ
  | 0, _, _ => isEmptyElim
  | K + 1, a, z => Fin.cases (normalizedQuery N (frame K a 0))
      (fun j => proposalQueryColumns r N frame update K (update K a z.1) z.2 j)

@[expose] def proposalOffColumns {Ambient : Type} [Fintype Ambient] {Past : Type*}
    (r : ℕ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (K : ℕ) → Past → StoppedNoise Ambient K → Fin K → Ambient → ℝ
  | 0, _, _ => isEmptyElim
  | K + 1, a, z => Fin.cases
      (((tailRows (frame K a))ᵀ * tailRows (frame K a)) *ᵥ (fun i => z.1 (.inl i)))
      (fun j => proposalOffColumns r frame update K (update K a z.1) z.2 j)

@[expose] def proposalDiagonalColumns {Ambient : Type} {Past : Type*}
    (N : ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past) :
    (K : ℕ) → Past → StoppedNoise Ambient K → Fin K → ℝ
  | 0, _, _ => isEmptyElim
  | K + 1, a, z => Fin.cases (2 * skSigma N * z.1 (.inr ()))
      (fun j => proposalDiagonalColumns N update K (update K a z.1) z.2 j)

@[expose] def proposalResidualMatrix {Ambient : Type} [Fintype Ambient] {Past : Type*}
    (r : ℕ) (N : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) : Matrix Ambient Ambient ℝ :=
  let E := embedding 0 (proposalTerminalPast update K a z)
  (Eᵀ * E) * goeMatrix (skSigma N) (proposalResidualPrimitive K z) * (Eᵀ * E)

theorem normalizedTensorProposal_eq_columnAssembly {Ambient : Type} [Fintype Ambient]
    [DecidableEq Ambient] {Past : Type*} [MeasurableSpace Past]
    (r : ℕ) (N : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) :
    normalizedTensorProposal r N embedding frame update K a z =
      columnAssembly N (proposalQueryColumns r N frame update K a z)
        (proposalOffColumns r frame update K a z) (proposalDiagonalColumns N update K a z)
        (proposalResidualMatrix r N embedding update K a z) := by
  induction K generalizing a with
  | zero =>
    simp [normalizedTensorProposal, columnAssembly, proposalResidualMatrix,
      proposalTerminalPast, proposalResidualPrimitive]
  | succ K ih =>
    change normalizedColumnMatrix N (normalizedQuery N (frame K a 0))
      (((tailRows (frame K a))ᵀ * tailRows (frame K a)) *ᵥ (fun i => z.1 (.inl i)))
      (2 * skSigma N * z.1 (.inr ())) +
      normalizedTensorProposal r N embedding frame update K (update K a z.1) z.2 = _
    rw [ih]
    unfold columnAssembly
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [proposalQueryColumns, proposalOffColumns, proposalDiagonalColumns,
      Fin.cases_zero, Fin.cases_succ]
    have hres : proposalResidualMatrix r N embedding update (K + 1) a z =
        proposalResidualMatrix r N embedding update K (update K a z.1) z.2 := rfl
    rw [hres]
    unfold normalizedColumnMatrix
    abel

@[expose] def skColumnAssembly {Ambient : Type} [Fintype Ambient] {Past : Type*}
    (r : ℕ) (N : ℝ)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) : Matrix Ambient Ambient ℝ :=
  columnAssembly N (proposalQueryColumns r N frame update K a z)
    (proposalOffColumns r frame update K a z) (proposalDiagonalColumns N update K a z)
    (proposalResidualMatrix r N embedding update K a z)

theorem skColumnAssembly_eq_physical {Ambient : Type} [Fintype Ambient]
    [DecidableEq Ambient] {Past : Type*} [MeasurableSpace Past]
    (r : ℕ) (N : ℝ) (hN : 0 < N)
    (embedding : (k : ℕ) → Past → Matrix (Fin (r + k)) Ambient ℝ)
    (frame : (k : ℕ) → Past → Matrix (Fin (r + k + 1)) Ambient ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Ambient ⊕ Unit) → Past)
    (K : ℕ) (a : Past) (z : StoppedNoise Ambient K) :
    skColumnAssembly r N embedding frame update K a z =
      physicalTensorProposal r (skSigma N) embedding frame update K a z := by
  rw [physicalTensorProposal_SK_normalized r N hN,
    normalizedTensorProposal_eq_columnAssembly]
  rfl

variable {Past : Type*} [MeasurableSpace Past]

theorem skColumnAssembly_law (r K : ℕ) (N : ℝ) (hN : 0 < N)
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
      (skColumnAssembly r N embedding frame update K a) =
      (primitiveGaussian (Fin (r + K) × Fin (r + K))).map (goeMatrix (skSigma N)) := by
  have heq : skColumnAssembly r N embedding frame update K a =
      physicalTensorProposal r (skSigma N) embedding frame update K a := by
    funext z
    exact skColumnAssembly_eq_physical r N hN embedding frame update K a z
  rw [heq]
  exact physicalTensorProposal_law r K (skSigma N) embedding direction frame update
    hembedding hdirection hmeasframe hupdate hresorth horth hinitorth hframe hnext a

theorem skColumnAssembly_joint_law
    (μ : Measure Past) [SFinite μ] (r K : ℕ) (N : ℝ) (hN : 0 < N)
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
      (fun x => (x.1, skColumnAssembly r N embedding frame update K x.1 x.2)) =
      μ.prod ((primitiveGaussian (Fin (r + K) × Fin (r + K))).map
        (goeMatrix (skSigma N))) := by
  have heq : (fun x : Past × StoppedNoise (Fin (r + K)) K =>
      (x.1, skColumnAssembly r N embedding frame update K x.1 x.2)) =
      (fun x => (x.1,
        physicalTensorProposal r (skSigma N) embedding frame update K x.1 x.2)) := by
    funext x
    rw [skColumnAssembly_eq_physical r N hN]
  rw [heq]
  exact physicalTensorProposal_joint_law μ r K (skSigma N) embedding direction frame update
    hembedding hdirection hmeasframe hupdate hresorth horth hinitorth hframe hnext

end SKConstants.GaussianProposal
