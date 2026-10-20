module

public import SKConstants.GaussianProposalAmbientReconstruction
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace SKConstants.GaussianProposal

@[expose] def borderMatrix (n : ℕ) (c : Fin (n + 1) → ℝ) (R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => Fin.cases (c j)
    (fun i' => Fin.cases (c i'.succ) (fun j' => R i' j') j) i

@[expose] def tailRows {n : ℕ} {Ambient : Type*} (B : Matrix (Fin (n + 1)) Ambient ℝ) :
    Matrix (Fin n) Ambient ℝ := fun i j => B i.succ j

@[expose] def columnOffVector {n : ℕ} {Ambient : Type*}
    (B : Matrix (Fin (n + 1)) Ambient ℝ) (c : Fin (n + 1) → ℝ) : Ambient → ℝ :=
  fun i => ∑ k : Fin n, c k.succ * B k.succ i

theorem fillJoin_border (n : ℕ) (c : Fin (n + 1) → ℝ)
    (q : UpperPair (Fin n) → ℝ) :
    fillSymmetricMatrix (joinUpper n (c, q)) = borderMatrix n c (fillSymmetricMatrix q) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [fillSymmetricMatrix, sortedPair, joinUpper, upperPairSplit, borderMatrix]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp [fillSymmetricMatrix, sortedPair, joinUpper, upperPairSplit, borderMatrix]
    · by_cases hij : i' ≤ j'
      · have hs : i'.succ ≤ j'.succ := Fin.succ_le_succ_iff.mpr hij
        simp [fillSymmetricMatrix, sortedPair, min_eq_left hij, max_eq_right hij,
          min_eq_left hs, max_eq_right hs, joinUpper, upperPairSplit, borderMatrix]
      · have hji : j' ≤ i' := le_of_lt (lt_of_not_ge hij)
        have hs : j'.succ ≤ i'.succ := Fin.succ_le_succ_iff.mpr hji
        simp [fillSymmetricMatrix, sortedPair, min_eq_right hji, max_eq_left hji,
          min_eq_right hs, max_eq_left hs, joinUpper, upperPairSplit, borderMatrix]

theorem border_conjugation_decomposition {n : ℕ} {Ambient : Type*} [Fintype Ambient]
    (B : Matrix (Fin (n + 1)) Ambient ℝ) (c : Fin (n + 1) → ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    Bᵀ * borderMatrix n c R * B =
      c 0 • Matrix.vecMulVec (B 0) (B 0) +
      Matrix.vecMulVec (B 0) (columnOffVector B c) +
      Matrix.vecMulVec (columnOffVector B c) (B 0) +
      (tailRows B)ᵀ * R * tailRows B := by
  change (Fin (n + 1) → Ambient → ℝ) at B
  change (Fin n → Fin n → ℝ) at R
  ext i j
  change (∑ k : Fin (n + 1), (∑ l : Fin (n + 1), B l i * borderMatrix n c R l k) * B k j) =
    c 0 * (B 0 i * B 0 j) + B 0 i * (∑ k : Fin n, c k.succ * B k.succ j) +
      (∑ k : Fin n, c k.succ * B k.succ i) * B 0 j +
      ∑ k : Fin n, (∑ l : Fin n, B l.succ i * R l k) * B k.succ j
  rw [Fin.sum_univ_succ]
  simp only [borderMatrix, Fin.cases_zero]
  simp_rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  have hswap (k : Fin n) : B k.succ i * c k.succ = c k.succ * B k.succ i := by
    ring
  simp_rw [hswap, mul_assoc]
  ring

theorem columnOffVector_projected {n : ℕ} {Ambient : Type*} [Fintype Ambient]
    (B : Matrix (Fin (n + 1)) Ambient ℝ) (g : Ambient → ℝ) (scale : ℝ)
    (c : Fin (n + 1) → ℝ)
    (hc : ∀ k : Fin n, c k.succ = scale * dot (B k.succ) g) :
    columnOffVector B c = scale • (((tailRows B)ᵀ * tailRows B) *ᵥ g) := by
  ext i
  change (∑ k : Fin n, c k.succ * B k.succ i) =
    scale * (∑ j, (∑ k : Fin n, B k.succ i * B k.succ j) * g j)
  simp only [hc, dot]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem basisAssembly_join_decomposition (n : ℕ)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : Fin (n + 1) → ℝ) (q : UpperPair (Fin n) → ℝ) :
    basisAssembly B (joinUpper n (c, q)) =
      c 0 • Matrix.vecMulVec (B 0) (B 0) +
      Matrix.vecMulVec (B 0) (columnOffVector B c) +
      Matrix.vecMulVec (columnOffVector B c) (B 0) +
      (tailRows B)ᵀ * fillSymmetricMatrix q * tailRows B := by
  unfold basisAssembly
  rw [fillJoin_border]
  exact border_conjugation_decomposition B c (fillSymmetricMatrix q)

theorem tailProjection_eq_remove_first {n : ℕ} {Ambient : Type*} [Fintype Ambient]
    (B : Matrix (Fin (n + 1)) Ambient ℝ) :
    (tailRows B)ᵀ * tailRows B = Bᵀ * B - Matrix.vecMulVec (B 0) (B 0) := by
  change (Fin (n + 1) → Ambient → ℝ) at B
  ext i j
  change (∑ k : Fin n, B k.succ i * B k.succ j) =
    (∑ k : Fin (n + 1), B k i * B k j) - B 0 i * B 0 j
  rw [Fin.sum_univ_succ]
  ring

theorem ambientColumn_zero {Ambient : Type} [Fintype Ambient] [DecidableEq Ambient]
    (sigma : ℝ) (n : ℕ) (frame : Fin (n + 1) → Ambient → ℝ)
    (z : EuclideanSpace ℝ (Ambient ⊕ Unit)) :
    ambientColumn sigma n frame z 0 = 2 * sigma * z (.inr ()) := by
  simp [ambientColumn, linearForm, ambientColumnCoefficients, Fintype.sum_sum_type]

theorem ambientColumn_succ {Ambient : Type} [Fintype Ambient] [DecidableEq Ambient]
    (sigma : ℝ) (n : ℕ) (frame : Fin (n + 1) → Ambient → ℝ)
    (z : EuclideanSpace ℝ (Ambient ⊕ Unit)) (j : Fin n) :
    ambientColumn sigma n frame z j.succ = Real.sqrt 2 * sigma *
      dot (frame j.succ) (fun i => z (.inl i)) := by
  simp [ambientColumn, linearForm, ambientColumnCoefficients, Fintype.sum_sum_type,
    dot, Finset.mul_sum, mul_assoc]

theorem ambientColumn_offVector {Ambient : Type} [Fintype Ambient] [DecidableEq Ambient]
    (sigma : ℝ) (n : ℕ) (frame : Matrix (Fin (n + 1)) Ambient ℝ)
    (z : EuclideanSpace ℝ (Ambient ⊕ Unit)) :
    columnOffVector frame (ambientColumn sigma n frame z) =
      (Real.sqrt 2 * sigma) • (((tailRows frame)ᵀ * tailRows frame) *ᵥ
        (fun i => z (.inl i))) :=
  columnOffVector_projected frame (fun i => z (.inl i)) (Real.sqrt 2 * sigma)
    (ambientColumn sigma n frame z) (ambientColumn_succ sigma n frame z)

end SKConstants.GaussianProposal
