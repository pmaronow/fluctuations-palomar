module

public import SKConstants.Completion.Y1.EarlierProjection
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine LQ N9 M1 LM5 Blueprint5 N9T1
variable {Ω : Type*} [MeasurableSpace Ω]

def paperRemovedRows {Past : Type*} (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past) :
    (K : ℕ) → PaperState r n K Past → StoppedNoise (Fin n) K →
      (e : Fin (K+1)) → Matrix (Fin e.val) (Fin n) ℝ
  | 0, _, _, e => fun i => False.elim (by have := i.isLt; have := e.isLt; omega)
  | K+1, s, z, e => Fin.cases (fun i => Fin.elim0 i)
      (fun e => Fin.cons (paperFrame s.2 (target K s.1) 0)
        (paperRemovedRows r n target update K
          (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 e)) e

theorem paperRemovedRows_unit {Past : Type*} (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (hs : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0)
    (e : Fin (K+1)) (j : Fin e.val) :
    dot (paperRemovedRows r n target update K s z e j)
      (paperRemovedRows r n target update K s z e j) = 1 := by
  induction K with
  | zero => have := j.isLt; have := e.isLt; omega
  | succ K ih =>
    revert j
    refine Fin.cases (fun j => Fin.elim0 j) (fun e => ?_) e
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [paperRemovedRows,Fin.cases_succ,Fin.cons_zero,ite_true] using
        paperFrame_orthogonal s.2 (target K s.1) hs 0 0
    · simpa only [paperRemovedRows,Fin.cases_succ,Fin.cons_succ] using
        ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2
          (tailRows_orthogonal _ (paperFrame_orthogonal _ _ hs)) e j

theorem frameProjection_cons {m n : ℕ} (v : Fin n → ℝ)
    (E : Matrix (Fin m) (Fin n) ℝ) :
    frameProjection (Fin.cons v E) = Matrix.vecMulVec v v + frameProjection E := by
  ext i j
  simp only [frameProjection,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,Matrix.add_apply,Matrix.vecMulVec_apply]

theorem paperRemovedRows_projection {Past : Type*} (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (e : Fin (K+1)) :
    frameProjection (paperRemovedRows r n target update K s z e) =
      frameProjection s.2-paperRemainingProjectionTrace r n target update K s z e := by
  induction K with
  | zero =>
    have he : e=0 := Fin.eq_zero e
    subst e
    simp [paperRemovedRows,paperRemainingProjectionTrace,frameProjection,Matrix.mul_apply]
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · simp [paperRemovedRows,paperRemainingProjectionTrace,frameProjection,Matrix.mul_apply]
    · let F := paperFrame s.2 (target K s.1)
      have he : frameProjection s.2 = Matrix.vecMulVec (F 0) (F 0)+frameProjection (tailRows F) := by
        rw [← paperFrame_projection s.2 (target K s.1)]
        exact frameProjection_eq_first_add_remaining F
      change frameProjection (Fin.cons (F 0)
        (paperRemovedRows r n target update K (update K s.1 z.1,tailRows F) z.2 e)) =
        frameProjection s.2-paperRemainingProjectionTrace r n target update K
          (update K s.1 z.1,tailRows F) z.2 e
      rw [frameProjection_cons,ih,he]
      abel

def earlierRemovedFrame (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    Matrix (Fin e.val) (Fin (r+K)) ℝ :=
  paperRemovedRows r (r+K)
    (fun k p => pastTarget W β hβ δ (growingQueryTime δ e.val) (K-1-k) p)
    (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K) e.castSucc

theorem earlierRemovedFrame_unit (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) (j : Fin e.val) :
    (∑ i, earlierRemovedFrame W β hβ δ r K e p j i^2) = 1 := by
  simpa only [earlierRemovedFrame,dot,pow_two] using
    paperRemovedRows_unit r (r+K)
      (fun k p => pastTarget W β hβ δ (growingQueryTime δ e.val) (K-1-k) p)
      (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K)
      (by intro i j; simp [dot,Matrix.one_apply]) e.castSucc j

theorem earlierCellProjection_eq_trace (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    earlierCellProjection W β hβ δ r K e p =
      paperRemainingProjectionTrace r (r+K)
        (fun k p => pastTarget W β hβ δ (growingQueryTime δ e.val) (K-1-k) p)
        (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K) e.castSucc := by
  unfold earlierCellProjection earlierCellFrame
  rw [frameProjection_castRows]
  exact paperStateBefore_projection r (r+K) _ _ K (p,1) _ _

theorem earlierRemovedFrame_projection (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    frameProjection (earlierRemovedFrame W β hβ δ r K e p) =
      1-earlierCellProjection W β hβ δ r K e p := by
  rw [earlierCellProjection_eq_trace]
  simpa only [earlierRemovedFrame,frameProjection,Matrix.transpose_one,Matrix.one_mul] using
    paperRemovedRows_projection r (r+K)
      (fun k p => pastTarget W β hβ δ (growingQueryTime δ e.val) (K-1-k) p)
      (fun _ p _ => p) K (p,1) (zeroStoppedNoise (r+K) K) e.castSucc

theorem earlierCellProjection_symm (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    (earlierCellProjection W β hβ δ r K e p).IsSymm := by
  rw [earlierCellProjection_eq_trace]
  exact paperRemainingProjectionTrace_symm r (r+K) _ _ K _ _ _

theorem earlierCellProjection_idempotent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) :
    earlierCellProjection W β hβ δ r K e p*earlierCellProjection W β hβ δ r K e p =
      earlierCellProjection W β hβ δ r K e p := by
  rw [earlierCellProjection_eq_trace]
  apply paperRemainingProjectionTrace_idempotent
  intro i j
  simp [dot,Matrix.one_apply]

theorem complement_projection_square_eq_rows {m n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hs : P.IsSymm) (hi : P*P=P)
    (E : Matrix (Fin m) (Fin n) ℝ) (hE : frameProjection E=1-P) (x : Fin n → ℝ) :
    dot ((1-P)*ᵥx) ((1-P)*ᵥx) = ∑ j, (∑ i, E j i*x i)^2 := by
  let Q := (1 : Matrix (Fin n) (Fin n) ℝ)-P
  have hQ : Q*Q=Q := by
    dsimp [Q]
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one,hi]
    abel
  have hQs : Qᵀ=Q := by
    change (1-P)ᵀ=1-P
    rw [Matrix.transpose_sub,Matrix.transpose_one,show Pᵀ=P from hs]
  have hdot : dot (Q*ᵥx) (Q*ᵥx) = dot x (Q*ᵥx) := by
    change (Q*ᵥx) ⬝ᵥ (Q*ᵥx) = x ⬝ᵥ (Q*ᵥx)
    rw [Matrix.dotProduct_mulVec]
    have hv : (Q*ᵥx) ᵥ* Q = Q*ᵥ(Q*ᵥx) := by
      calc
        _ = (Q*ᵥx) ᵥ* Qᵀ := by rw [hQs]
        _ = _ := Matrix.vecMul_transpose Q (Q*ᵥx)
    rw [hv,Matrix.mulVec_mulVec,hQ,dotProduct_comm]
  calc
    _ = dot x (Q*ᵥx) := hdot
    _ = dot (E*ᵥx) (E*ᵥx) := by
      change x ⬝ᵥ (Q*ᵥx) = (E*ᵥx) ⬝ᵥ (E*ᵥx)
      dsimp only [Q]
      rw [← hE]
      change x ⬝ᵥ ((Eᵀ*E)*ᵥx) = _
      rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    _ = _ := by simp only [dot,Matrix.mulVec,dotProduct,pow_two]

end SKConstants.Completion.Y1
