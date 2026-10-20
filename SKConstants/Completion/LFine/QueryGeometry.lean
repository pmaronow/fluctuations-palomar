module

public import SKConstants.GaussianProposalGramStability
public import SKConstants.GaussianProposalPaperRevelation
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Matrix

namespace SKConstants.Completion.LFine
open GaussianProposal

def queryResidualNorm {m n : ℕ} (N : ℝ)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ) : ℝ :=
  Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)) / Real.sqrt N

theorem paperFrame_query_dot_target {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    dot (paperFrame E t 0) t = Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)) := by
  rw [paperFrame_designated_row E t hE]
  change (paperDirection E t ᵥ* E) ⬝ᵥ t = _
  rw [← Matrix.dotProduct_mulVec]
  by_cases hz : E *ᵥ t = 0
  · simp [hz, dot]
  · simp only [paperDirection, hz, ↓reduceIte, unitNormalize, smul_dotProduct,
      smul_eq_mul]
    have hp : 0 < dot (E *ᵥ t) (E *ᵥ t) :=
      lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm (by
        intro h; exact hz ((dot_self_eq_zero_iff _).mp h)))
    have hs := (Real.sqrt_pos.mpr hp).ne'
    have hsq := Real.sq_sqrt hp.le
    change (Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)))⁻¹ * dot (E *ᵥ t) (E *ᵥ t) = _
    calc
      _ = (Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)))⁻¹ *
          (Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)))^2 := by rw [hsq]
      _ = _ := by field_simp

theorem paperFrame_remaining_kills_target {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    remainingProjection (paperFrame E t) *ᵥ t = 0 := by
  have hF := paperFrame_orthogonal E t hE
  have hsupport := remainingProjection_mul_frameProjection (paperFrame E t) hF
  rw [paperFrame_projection E t] at hsupport
  have hproj : remainingProjection (paperFrame E t) *ᵥ t =
      remainingProjection (paperFrame E t) *ᵥ (frameProjection E *ᵥ t) := by
    rw [Matrix.mulVec_mulVec, hsupport]
  rw [hproj]
  by_cases hz : E *ᵥ t = 0
  · simp [frameProjection, ← Matrix.mulVec_mulVec, hz]
  · have hp : 0 < dot (E *ᵥ t) (E *ᵥ t) :=
      lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm (by
        intro h; exact hz ((dot_self_eq_zero_iff _).mp h)))
    have hs := (Real.sqrt_pos.mpr hp).ne'
    have hrow := paperFrame_projected_target E t hE hz
    have heq : frameProjection E *ᵥ t =
        Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)) • paperFrame E t 0 := by
      rw [hrow, smul_smul, mul_inv_cancel₀ hs, one_smul]
      rfl
    rw [heq, Matrix.mulVec_smul, remainingProjection_query _ hF, smul_zero]

theorem paperFrame_inherits_killed_mean {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t m₀ : Fin n → ℝ)
    (hm₀ : E *ᵥ m₀ = 0) :
    paperFrame E t *ᵥ m₀ = 0 := by
  unfold paperFrame
  rw [← Matrix.mulVec_mulVec, hm₀, Matrix.mulVec_zero]

theorem paperFrame_remaining_kills_mean {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t m₀ : Fin n → ℝ) (s : ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0)
    (hm₀ : E *ᵥ m₀ = 0) :
    remainingProjection (paperFrame E t) *ᵥ (m₀ + s • t) = 0 := by
  have hmean := paperFrame_inherits_killed_mean E t m₀ hm₀
  have htail : tailRows (paperFrame E t) *ᵥ m₀ = 0 := by
    ext i
    exact congrFun hmean i.succ
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, paperFrame_remaining_kills_target E t hE,
    smul_zero, add_zero]
  unfold remainingProjection
  rw [← Matrix.mulVec_mulVec, htail, Matrix.mulVec_zero]

theorem paperFrame_query_dot_mean {m n : ℕ} (N : ℝ) (hN : 0 < N)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t m₀ : Fin n → ℝ) (s : ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0)
    (hm₀ : E *ᵥ m₀ = 0) :
    N⁻¹ * dot (normalizedQuery N (paperFrame E t 0)) (m₀ + s • t) =
      s * queryResidualNorm N E t := by
  have hz : dot (paperFrame E t 0) m₀ = 0 :=
    congrFun (paperFrame_inherits_killed_mean E t m₀ hm₀) 0
  have hs := (Real.sqrt_pos.mpr hN).ne'
  have hscale : N⁻¹ * Real.sqrt N = (Real.sqrt N)⁻¹ := by
    calc
      _ = ((Real.sqrt N)^2)⁻¹ * Real.sqrt N := by rw [Real.sq_sqrt hN.le]
      _ = _ := by field_simp
  change N⁻¹ * ((Real.sqrt N • paperFrame E t 0) ⬝ᵥ (m₀ + s • t)) = _
  have hzt : paperFrame E t 0 ⬝ᵥ m₀ = 0 := hz
  have hqt : paperFrame E t 0 ⬝ᵥ t = Real.sqrt (dot (E *ᵥ t) (E *ᵥ t)) :=
    paperFrame_query_dot_target E t hE
  simp only [smul_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul,
    hzt, hqt]
  unfold queryResidualNorm
  calc
    _ = (N⁻¹ * Real.sqrt N) * (s * Real.sqrt (dot (E *ᵥ t) (E *ᵥ t))) := by ring
    _ = _ := by rw [hscale]; ring

theorem paperFrame_mean_killed_sum {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t m₀ : Fin n → ℝ) (s : ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0)
    (hm₀ : E *ᵥ m₀ = 0) (i : Fin n) :
    (∑ j, remainingProjection (paperFrame E t) j i * (m₀ + s • t) j) = 0 := by
  have h := congrFun (paperFrame_remaining_kills_mean E t m₀ s hE hm₀) i
  change (∑ j, remainingProjection (paperFrame E t) i j * (m₀ + s • t) j) = 0 at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [remainingProjection, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

end SKConstants.Completion.LFine
