module

public import SKConstants.Completion.Blueprint5.ContinuityStatements
public import SKConstants.Completion.N13a.Positions
import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped NNReal BigOperators
namespace SKConstants.Completion.N19C
open GaussianProposal Blueprint N19 N19n
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def completionTrace (n q : ℕ) (a : PaperCompletionNoise n q) (j : Fin q) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i =>
    paperNoiseTrace n q (paperCompletionReplayNoise n q a) j (.inl i))

theorem completionTrace_eq (n q : ℕ) (a : PaperCompletionNoise n q) (j : Fin q) :
    completionTrace n q a j = N13a.coarsePrefix_completionAt n q a j := by
  induction q with
  | zero => exact Fin.elim0 j
  | succ q ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact ih a.2 k

theorem completionAt_norm_sq_le (n q : ℕ) (R : ℝ) (a : PaperCompletionNoise n q)
    (ha : paperCompletionNormCap n R q a) (j : Fin q) :
    ‖N13a.coarsePrefix_completionAt n q a j‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
  induction q with
  | zero => exact Fin.elim0 j
  | succ q ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · exact ha.1
    · exact ih a.2 ha.2 k

theorem completionAt_norm_le (n q : ℕ) (R : ℝ) (a : PaperCompletionNoise n q)
    (ha : paperCompletionNormCap n R q a) (j : Fin q) :
    ‖N13a.coarsePrefix_completionAt n q a j‖ ≤ Real.sqrt n * |R| := by
  have hs := completionAt_norm_sq_le n q R a ha j
  have he : (Real.sqrt n * |R|) ^ 2 = (n : ℝ) * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), sq_abs]
  have hn : 0 ≤ Real.sqrt n * |R| := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  nlinarith [norm_nonneg (N13a.coarsePrefix_completionAt n q a j)]

theorem completionAt_comb (n q : ℕ) (c s : ℝ) (a b : PaperCompletionNoise n q)
    (j : Fin q) :
    N13a.coarsePrefix_completionAt n q (completionComb c s q a b) j =
      c • N13a.coarsePrefix_completionAt n q a j +
        s • N13a.coarsePrefix_completionAt n q b j := by
  induction q with
  | zero => exact Fin.elim0 j
  | succ q ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact ih a.2 b.2 k

theorem completionTrace_castAux_norm (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m)
    (a : N13a.PrefixAux δ n q) (j : Fin q) :
    ‖completionTrace m q (N13a.coarsePrefix_castAux δ q h a).2.1 j‖ =
      ‖completionTrace n q a.2.1 j‖ := by
  subst m
  rfl

theorem completionTrace_castAux_sub_norm (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m)
    (a b : N13a.PrefixAux δ n q) (j : Fin q) :
    ‖completionTrace m q (N13a.coarsePrefix_castAux δ q h a).2.1 j -
        completionTrace m q (N13a.coarsePrefix_castAux δ q h b).2.1 j‖ =
      ‖completionTrace n q a.2.1 j - completionTrace n q b.2.1 j‖ := by
  subst m
  rfl

theorem completionTrace_coarseAux_norm (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf + qf = rb + qb) (hq : qb ≤ qf) (a : ReplayAux δ rf qf) (j : Fin qb) :
    ‖completionTrace (rb + qb) qb
        (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq a).2.1 j‖ =
      ‖N13a.coarsePrefix_completionAt (rf + qf) qf a.2.1 (Fin.castLE hq j)‖ := by
  unfold N13a.coarsePrefix_replayAux
  rw [Function.comp_apply, completionTrace_castAux_norm]
  change ‖completionTrace (rf + qf) qb
    (N13a.coarsePrefix_completion (rf + qf) qf qb hq a.2.1) j‖ = _
  rw [completionTrace_eq, N13a.coarsePrefix_completion_position]

theorem completionTrace_coarseAux_sub_norm (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf + qf = rb + qb) (hq : qb ≤ qf) (a b : ReplayAux δ rf qf) (j : Fin qb) :
    ‖completionTrace (rb + qb) qb
        (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq a).2.1 j -
      completionTrace (rb + qb) qb
        (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq b).2.1 j‖ =
      ‖N13a.coarsePrefix_completionAt (rf + qf) qf a.2.1 (Fin.castLE hq j) -
        N13a.coarsePrefix_completionAt (rf + qf) qf b.2.1 (Fin.castLE hq j)‖ := by
  unfold N13a.coarsePrefix_replayAux
  rw [Function.comp_apply, Function.comp_apply, completionTrace_castAux_sub_norm]
  change ‖completionTrace (rf + qf) qb
      (N13a.coarsePrefix_completion (rf + qf) qf qb hq a.2.1) j -
    completionTrace (rf + qf) qb
      (N13a.coarsePrefix_completion (rf + qf) qf qb hq b.2.1) j‖ = _
  rw [completionTrace_eq, completionTrace_eq, N13a.coarsePrefix_completion_position,
    N13a.coarsePrefix_completion_position]

end SKConstants.Completion.N19C
