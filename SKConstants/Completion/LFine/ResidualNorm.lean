module

public import SKConstants.Completion.LFine.QueryGeometry
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix

namespace SKConstants.Completion.LFine
open GaussianProposal

theorem frameProjection_target_norm_square {m n : ℕ}
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    dot (frameProjection E *ᵥ t) (frameProjection E *ᵥ t) = dot (E *ᵥ t) (E *ᵥ t) := by
  simp only [frameProjection,← Matrix.mulVec_mulVec]
  change ((Eᵀ *ᵥ (E *ᵥ t)) ⬝ᵥ (Eᵀ *ᵥ (E *ᵥ t))) = _
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,Matrix.mulVec_mulVec,
    frame_mul_transpose E hE,Matrix.one_mulVec]
  rfl

theorem queryResidualNorm_eq_projected_norm {m n : ℕ} (N : ℝ)
    (E : Matrix (Fin (m+1)) (Fin n) ℝ) (t : Fin n → ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0) :
    queryResidualNorm N E t =
      ‖WithLp.toLp 2 (frameProjection E *ᵥ t)‖ / Real.sqrt N := by
  unfold queryResidualNorm
  rw [← frameProjection_target_norm_square E t hE,
    ← euclidean_norm_sq_dot,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

end SKConstants.Completion.LFine
