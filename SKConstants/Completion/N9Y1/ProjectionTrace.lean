module

public import SKConstants.Completion.N9Y1.Regularity
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation M1 LM5 Blueprint5

theorem frameProjection_trace {m n : ℕ} (E : Matrix (Fin m) (Fin n) ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    (∑ i, frameProjection E i i) = (m : ℝ) := by
  simp only [frameProjection,Matrix.mul_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]
  have hrow (j : Fin m) : (∑ i, E j i*E j i) = 1 := by
    simpa only [dot,ite_true] using hE j j
  simp [hrow]

theorem paperRemainingProjectionTrace_trace {Past : Type*} (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (K : ℕ) (s : PaperState r n K Past) (z : StoppedNoise (Fin n) K)
    (horth : ∀ i j, dot (s.2 i) (s.2 j) = if i=j then 1 else 0) (j : Fin (K+1)) :
    (∑ i, paperRemainingProjectionTrace r n target update K s z j i i) =
      (r+K : ℕ)-(j.val : ℝ) := by
  induction K with
  | zero =>
    have hj : j=0 := Fin.ext (by have := j.isLt; omega)
    subst j
    simpa only [paperRemainingProjectionTrace,Fin.val_zero,Nat.add_zero,
      Nat.cast_zero,sub_zero] using frameProjection_trace s.2 horth
  | succ K ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [paperRemainingProjectionTrace,Fin.cases_zero,Fin.val_zero,
        Nat.cast_zero,sub_zero] using frameProjection_trace s.2 horth
    · have he := ih (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2
        (tailRows_orthogonal _ (paperFrame_orthogonal _ _ horth)) j
      change (∑ i, paperRemainingProjectionTrace r n target update K
        (update K s.1 z.1,tailRows (paperFrame s.2 (target K s.1))) z.2 j i i) = _
      rw [he]
      simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
      ring

variable {Ω : Type*} [MeasurableSpace Ω]

theorem fineCellRemainingProjection_trace_deficit (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    (∑ i, ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) -
      fineCellRemainingProjection W β hβ δ r K e z) i i) = (e.val : ℝ) := by
  have hI : ∀ i j : Fin (r+K),
      dot ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) i)
        ((1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ) j) = if i=j then 1 else 0 := by
    intro i j
    simp [dot,Matrix.one_apply]
  have ht := paperRemainingProjectionTrace_trace r (r+K)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) K
    (growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) hI e.castSucc
  simp only [Matrix.sub_apply,Matrix.one_apply_eq]
  rw [Finset.sum_sub_distrib]
  change (∑ _ : Fin (r+K), (1 : ℝ)) -
    (∑ i, paperRemainingProjectionTrace r (r+K) (M1.Target W β hβ δ r K)
      (M1.Update δ r K) K (growingInitial δ r K z.2.1,1)
        (M1.Original δ r K z.2) e.castSucc i i) = _
  rw [ht]
  simp

theorem fineCellRemainingProjection_eq_one_of_val_zero (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K) (he : e.val=0)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    fineCellRemainingProjection W β hβ δ r K e z = 1 := by
  have hz : e.castSucc=0 := Fin.ext he
  unfold fineCellRemainingProjection
  rw [hz,GaussianProposal.paperRemainingProjectionTrace_zero]
  simp [frameProjection]

theorem fineCellRemovedSquare_eq_zero_of_val_zero (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K) (he : e.val=0)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    fineCellRemovedSquare W β hβ δ r K e z = 0 := by
  unfold fineCellRemovedSquare
  rw [fineCellRemainingProjection_eq_one_of_val_zero W β hβ δ r K e he z]
  simp [dot]

end SKConstants.Completion.N9Y1
