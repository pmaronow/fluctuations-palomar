module

public import SKConstants.GaussianProposalScalarCallbacks
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace SKConstants.GaussianProposal
set_option backward.isDefEq.respectTransparency false
variable {Past : Type*}

def paperQueryDirectionTrace (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K → Fin K → Fin n → ℝ
  | 0, _, _ => fun j => Fin.elim0 j
  | K+1, s, z =>
    let F := paperFrame s.2 (target K s.1)
    Fin.cases (normalizedQuery N (F 0))
      (paperQueryDirectionTrace r n N target update K
        (update K s.1 z.1,tailRows F) z.2)

def paperRemainingProjectionTrace (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K → Fin (K+1) →
      Matrix (Fin n) (Fin n) ℝ
  | 0, s, _ => fun _ => frameProjection s.2
  | K+1, s, z =>
    let F := paperFrame s.2 (target K s.1)
    Fin.cases (frameProjection s.2)
      (paperRemainingProjectionTrace r n target update K
        (update K s.1 z.1,tailRows F) z.2)

def paperScalarPastTrace (r n : ℕ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K → Fin (K+1) → Past
  | 0, s, _ => fun _ => s.1
  | K+1, s, z =>
    let F := paperFrame s.2 (target K s.1)
    Fin.cases s.1 (paperScalarPastTrace r n target update K
      (update K s.1 z.1,tailRows F) z.2)

lemma frameProjection_eq_first_add_remaining {m n : ℕ}
    (F : Matrix (Fin (m+1)) (Fin n) ℝ) :
    frameProjection F = Matrix.vecMulVec (F 0) (F 0) + remainingProjection F := by
  ext i j
  simp only [frameProjection,remainingProjection,Matrix.mul_apply,Matrix.transpose_apply,
    Matrix.add_apply,Matrix.vecMulVec_apply,Fin.sum_univ_succ,tailRows]

lemma inverse_scale_query_outer (N : ℝ) (hN : 0 < N) {n : ℕ} (u : Fin n → ℝ) :
    N⁻¹ • Matrix.vecMulVec (normalizedQuery N u) (normalizedQuery N u) =
      Matrix.vecMulVec u u := by
  ext i j
  simp only [normalizedQuery,Matrix.smul_apply,Matrix.vecMulVec_apply,
    Pi.smul_apply,smul_eq_mul]
  have hs := Real.sq_sqrt hN.le
  calc
    _ = (N⁻¹ * (Real.sqrt N)^2)*(u i*u j) := by ring
    _ = _ := by rw [hs,inv_mul_cancel₀ hN.ne',one_mul]

theorem paperRemainingProjectionTrace_eq_prefix (r n : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (j : Fin (K+1)) :
    paperRemainingProjectionTrace r n target update K s z j = frameProjection s.2 -
      ∑ i : Fin K, if i.val < j.val then
        N⁻¹ • Matrix.vecMulVec (paperQueryDirectionTrace r n N target update K s z i)
          (paperQueryDirectionTrace r n N target update K s z i) else 0 := by
  induction K with
  | zero => simp [paperRemainingProjectionTrace]
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [paperRemainingProjectionTrace]
    · have hi := ih (update K s.1 z.1,tailRows F) z.2 j
      have hframe : frameProjection s.2 =
          N⁻¹ • Matrix.vecMulVec (normalizedQuery N (F 0)) (normalizedQuery N (F 0)) +
            frameProjection (tailRows F) := by
        rw [inverse_scale_query_outer N hN]
        rw [← paperFrame_projection s.2 (target K s.1)]
        exact frameProjection_eq_first_add_remaining F
      change paperRemainingProjectionTrace r n target update K
        (update K s.1 z.1,tailRows F) z.2 j = _
      rw [hi,hframe]
      simp only [Fin.sum_univ_succ,paperQueryDirectionTrace,Fin.cases_zero,Fin.cases_succ,
        Fin.val_zero,Fin.val_succ,Nat.zero_lt_succ,Nat.succ_lt_succ_iff,ite_true]
      abel

theorem actualPaper_remainingProjection_eq_past_queries (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) (j : Fin (K+1)) :
    paperRemainingProjectionTrace r (r+K) target update K (a,1) z j =
      1 - ∑ i : Fin K, if i.val < j.val then
        N⁻¹ • Matrix.vecMulVec
          (paperQueryDirectionTrace r (r+K) N target update K (a,1) z i)
          (paperQueryDirectionTrace r (r+K) N target update K (a,1) z i) else 0 := by
  simpa only [frameProjection,Matrix.transpose_one,Matrix.one_mul] using
    paperRemainingProjectionTrace_eq_prefix r (r+K) N hN target update K (a,1) z j

end SKConstants.GaussianProposal
