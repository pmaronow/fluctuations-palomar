module

public import SKConstants.GaussianProposalGramStability
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.GaussianProposal
variable {Past : Type*} [MeasurableSpace Past]

def paperMatrixQueryNoiseRun (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K →
      Matrix (Fin n) (Fin n) ℝ → StoppedNoise (Fin n) K
  | 0, _, z, _ => z
  | K+1, s, z, W =>
    let F := paperFrame s.2 (target K s.1)
    let g := paperQueriedNoise N F W z.1
    (g,paperMatrixQueryNoiseRun r n N target update K
      (update K s.1 g,tailRows F) z.2 W)

theorem paperMatrixQueryRun_eq_replayed_terminal (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    paperMatrixQueryRun r n N target update K s z W =
      proposalTerminalPast update K s.1
        (paperMatrixQueryNoiseRun r n N target update K s z W) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    exact ih (update K s.1 (paperQueriedNoise N (paperFrame s.2 (target K s.1)) W z.1),
      tailRows (paperFrame s.2 (target K s.1))) z.2

theorem paperMatrixQueryNoiseRun_eq_generated (r n : ℕ) (N : ℝ) (hN : 0<N)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (z : StoppedNoise (Fin n) K) (W : Matrix (Fin n) (Fin n) ℝ)
    (hcomp : frameProjection s.2 * W * frameProjection s.2 =
      paperTensorProposal r n (skSigma N) target update K s z) :
    paperMatrixQueryNoiseRun r n N target update K s z W = z := by
  induction K generalizing W with
  | zero => rfl
  | succ K ih =>
    let F := paperFrame s.2 (target K s.1)
    have hF : ∀ i j, dot (F i) (F j) = if i=j then 1 else 0 :=
      paperFrame_orthogonal s.2 (target K s.1) horth
    have hg : paperQueriedNoise N F W z.1 = z.1 := by
      ext i
      cases i with
      | inl i => exact congrFun (matrix_query_completed_endpoint_of_compression
          r n K N hN target update s horth z W hcomp) i
      | inr i => cases i; rfl
    change (paperQueriedNoise N F W z.1,
      paperMatrixQueryNoiseRun r n N target update K
        (update K s.1 (paperQueriedNoise N F W z.1),tailRows F) z.2 W) = z
    rw [hg]
    apply Prod.ext
    · rfl
    · apply ih (update K s.1 z.1,tailRows F) (tailRows_orthogonal F hF) z.2 W
      exact matrix_remaining_compression_of_compression r n K (skSigma N) target update
        s horth z W hcomp

theorem actualPaperProposal_matrixQueryNoiseRun_eq (r K : ℕ) (N : ℝ) (hN : 0<N)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) :
    paperMatrixQueryNoiseRun r (r+K) N target update K (a,1) z
      (actualPaperProposal r K (skSigma N) target update a z) = z := by
  have horth : ∀ i j : Fin (r+K),
      dot ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) i)
        ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) j) = if i=j then 1 else 0 := by
    intro i j
    have hId : (1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) = canonicalBasis := by
      ext i j
      exact Matrix.one_apply
    rw [hId]
    exact canonicalBasis_orthogonal i j
  apply paperMatrixQueryNoiseRun_eq_generated r (r+K) N hN target update K (a,1) horth z
  simp only [frameProjection,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
  rfl

def paperMatrixQueryTargetTrace (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (W : Matrix (Fin n) (Fin n) ℝ) : Fin K → Fin n → ℝ :=
  paperTargetTrace r n target update K s (paperMatrixQueryNoiseRun r n N target update K s z W)

def paperMatrixQueryDirectionTrace (r n : ℕ) (N : ℝ)
    (target : (k : ℕ) → Past → Fin n → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (W : Matrix (Fin n) (Fin n) ℝ) : Fin K → Fin n → ℝ :=
  paperQueryDirectionTrace r n 1 target update K s
    (paperMatrixQueryNoiseRun r n N target update K s z W)

theorem actualPaperProposal_matrixQueryTargetTrace_eq (r K : ℕ) (N : ℝ) (hN : 0<N)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) :
    paperMatrixQueryTargetTrace r (r+K) N target update K (a,1) z
      (actualPaperProposal r K (skSigma N) target update a z) =
        paperTargetTrace r (r+K) target update K (a,1) z := by
  unfold paperMatrixQueryTargetTrace
  rw [actualPaperProposal_matrixQueryNoiseRun_eq r K N hN]

theorem actualPaperProposal_matrixQueryDirectionTrace_eq (r K : ℕ) (N : ℝ) (hN : 0<N)
    (target : (k : ℕ) → Past → Fin (r+K) → ℝ)
    (update : (k : ℕ) → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (a : Past) (z : StoppedNoise (Fin (r+K)) K) :
    paperMatrixQueryDirectionTrace r (r+K) N target update K (a,1) z
      (actualPaperProposal r K (skSigma N) target update a z) =
        paperQueryDirectionTrace r (r+K) 1 target update K (a,1) z := by
  unfold paperMatrixQueryDirectionTrace
  rw [actualPaperProposal_matrixQueryNoiseRun_eq r K N hN]

end SKConstants.GaussianProposal
