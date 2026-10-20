module

public import SKConstants.Completion.LFine.QueryGeometry
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace SKConstants.Completion.LFine
open GaussianProposal

theorem paperFrame_tail_kills_target {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    tailRows (paperFrame E t) *ᵥ t = 0 := by
  have htail := tailRows_orthogonal (paperFrame E t) (paperFrame_orthogonal E t hE)
  have hp : frameProjection (tailRows (paperFrame E t)) *ᵥ t = 0 :=
    paperFrame_remaining_kills_target E t hE
  calc
    _ = tailRows (paperFrame E t) *ᵥ
        (frameProjection (tailRows (paperFrame E t)) *ᵥ t) := by
      rw [Matrix.mulVec_mulVec, frame_mul_projection _ htail]
    _ = 0 := by rw [hp, Matrix.mulVec_zero]

variable {Past : Type*}

theorem paperProjection_preserves_killing (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (v : Fin n → ℝ) (hkilled : s.2 *ᵥ v = 0) (k : Fin (K+1)) :
    paperRemainingProjectionTrace r n target update K s z k *ᵥ v = 0 := by
  induction K with
  | zero =>
    change frameProjection s.2 *ᵥ v = 0
    simp [frameProjection, ← Matrix.mulVec_mulVec, hkilled]
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    refine Fin.cases ?_ (fun k => ?_) k
    · change frameProjection s.2 *ᵥ v = 0
      simp [frameProjection, ← Matrix.mulVec_mulVec, hkilled]
    · have ht : tailRows F *ᵥ v = 0 := by
        ext i
        exact congrFun (paperFrame_inherits_killed_mean s.2 (target K s.1) v hkilled) i.succ
      exact ih (update K s.1 z.1,tailRows F) z.2 ht k

theorem paperProjection_kills_prior_target (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past)
    (hE : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (z : StoppedNoise (Fin n) K) (j : Fin K) (k : Fin (K+1))
    (hjk : j.val < k.val) :
    paperRemainingProjectionTrace r n target update K s z k *ᵥ
      paperTargetTrace r n target update K s z j = 0 := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    have htail := tailRows_orthogonal F (paperFrame_orthogonal s.2 (target K s.1) hE)
    revert hjk
    refine Fin.cases ?_ (fun j => ?_) j
    · refine Fin.cases ?_ (fun k _ => ?_) k
      · intro h
        exact False.elim (Nat.not_lt_zero _ h)
      · exact paperProjection_preserves_killing r n target update K
          (update K s.1 z.1,tailRows F) z.2 (target K s.1)
          (paperFrame_tail_kills_target s.2 (target K s.1) hE) k
    · refine Fin.cases ?_ (fun k h => ?_) k
      · intro h
        exact False.elim (Nat.not_lt_zero _ h)
      · exact ih (update K s.1 z.1,tailRows F) htail z.2 j k (by simpa using h)

theorem paperProjection_kills_target_telescope (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past)
    (hE : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (z : StoppedNoise (Fin n) K) (w : Fin K → ℝ) (k : Fin (K+1)) :
    paperRemainingProjectionTrace r n target update K s z k *ᵥ
      (∑ j : Fin K, if j.val < k.val then
        w j • paperTargetTrace r n target update K s z j else 0) = 0 := by
  rw [Matrix.mulVec_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val < k.val
  · rw [ite_eq_left hj, Matrix.mulVec_smul,
      paperProjection_kills_prior_target r n target update K s hE z j k hj, smul_zero]
  · rw [ite_eq_right hj, Matrix.mulVec_zero]

end SKConstants.Completion.LFine
