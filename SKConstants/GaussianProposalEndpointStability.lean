module

public import SKConstants.GaussianProposalGramStability
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic

@[expose] public section
noncomputable section
open NormedSpace InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator Classical
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.GaussianProposal

theorem symmetric_idempotent_apply_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (A : E →L[ℝ] E)
    (hs : (A : E →ₗ[ℝ] E).IsSymmetric) (hi : ∀ x, A (A x) = A x) (x : E) :
    ‖A x‖ ≤ ‖x‖ := by
  have he : ‖A x‖^2 = ⟪A x,x⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    have hh : ⟪A (A x),x⟫_ℝ = ⟪A x,A x⟫_ℝ := hs.apply_clm (A x) x
    rw [hi] at hh
    exact hh.symm
  have hb := abs_real_inner_le_norm (A x) x
  have hle := (le_abs_self ⟪A x,x⟫_ℝ).trans hb
  rw [←he] at hle
  nlinarith [norm_nonneg (A x), norm_nonneg x]

theorem frameProjection_apply_norm_le {m n : ℕ}
    (E : Matrix (Fin m) (Fin n) ℝ)
    (hE : ∀ i j, dot (E i) (E j) = if i=j then 1 else 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (frameProjection E) x‖ ≤ ‖x‖ := by
  apply symmetric_idempotent_apply_norm_le
  · change (frameProjection E).toEuclideanLin.IsSymmetric
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    change (Eᵀ*E)ᴴ = Eᵀ*E
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  · intro x
    have hid : frameProjection E * frameProjection E = frameProjection E := by
      unfold frameProjection
      calc
        _ = Eᵀ * (E*Eᵀ) * E := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [frame_mul_transpose E hE,Matrix.mul_one]
    have hm := congrArg (fun M => Matrix.toEuclideanCLM (𝕜 := ℝ) M x) hid
    simpa only [map_mul, ContinuousLinearMap.mul_apply] using hm

def completedMatrixEndpoint {n : ℕ} (P W : Matrix (Fin n) (Fin n) ℝ)
    (u z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) P
    (Matrix.toEuclideanCLM (𝕜 := ℝ) W u) +
      (1-Matrix.toEuclideanCLM (𝕜 := ℝ) P) z

theorem completedMatrixEndpoint_difference_le {n : ℕ}
    (P Q W W' : Matrix (Fin n) (Fin n) ℝ)
    (u v z : EuclideanSpace ℝ (Fin n))
    (hP : ∀ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P x‖ ≤ ‖x‖) :
    ‖completedMatrixEndpoint P W u z - completedMatrixEndpoint Q W' v z‖ ≤
      ‖W-W'‖*‖u‖ + ‖W'‖*‖u-v‖ + ‖P-Q‖*(‖W'‖*‖v‖+‖z‖) := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) P
  let B := Matrix.toEuclideanCLM (𝕜 := ℝ) Q
  let X := Matrix.toEuclideanCLM (𝕜 := ℝ) W
  let Y := Matrix.toEuclideanCLM (𝕜 := ℝ) W'
  have he : completedMatrixEndpoint P W u z - completedMatrixEndpoint Q W' v z =
      A ((X-Y) u) + A (Y (u-v)) + (A-B) (Y v-z) := by
    dsimp [completedMatrixEndpoint,A,B,X,Y]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      map_sub, map_add]
    abel
  rw [he]
  have ht := (norm_add_le (A ((X-Y) u)+A (Y (u-v))) ((A-B) (Y v-z))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  have h1 := (hP ((X-Y) u)).trans ((X-Y).le_opNorm u)
  have h2 := (hP (Y (u-v))).trans (Y.le_opNorm (u-v))
  have h3 := ((A-B).le_opNorm (Y v-z)).trans
    (mul_le_mul_of_nonneg_left ((norm_sub_le (Y v) z).trans
      (add_le_add (Y.le_opNorm v) le_rfl)) (norm_nonneg (A-B)))
  have hn1 : ‖X-Y‖ = ‖W-W'‖ := by
    rw [←map_sub]; exact Matrix.l2_opNorm_toEuclideanCLM _
  have hn2 : ‖Y‖ = ‖W'‖ := Matrix.l2_opNorm_toEuclideanCLM _
  have hn3 : ‖A-B‖ = ‖P-Q‖ := by
    rw [←map_sub]; exact Matrix.l2_opNorm_toEuclideanCLM _
  rw [hn1] at h1
  rw [hn2] at h2
  rw [hn2,hn3] at h3
  linarith

theorem completedMatrixEndpoint_difference_with_completion_le {n : ℕ}
    (P Q W W' : Matrix (Fin n) (Fin n) ℝ)
    (u v z z' : EuclideanSpace ℝ (Fin n))
    (hP : ∀ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P x‖≤‖x‖)
    (hQ : ∀ x, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Q x‖≤‖x‖) :
    ‖completedMatrixEndpoint P W u z-completedMatrixEndpoint Q W' v z'‖≤
      ‖W-W'‖*‖u‖+‖W'‖*‖u-v‖+‖P-Q‖*(‖W'‖*‖v‖+‖z‖)+2*‖z-z'‖ := by
  have h := completedMatrixEndpoint_difference_le P Q W W' u v z hP
  have he : completedMatrixEndpoint Q W' v z-completedMatrixEndpoint Q W' v z' =
      (z-z')-Matrix.toEuclideanCLM (𝕜 := ℝ) Q (z-z') := by
    unfold completedMatrixEndpoint
    simp only [map_sub,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply]
    abel
  have hc : ‖completedMatrixEndpoint Q W' v z-completedMatrixEndpoint Q W' v z'‖≤2*‖z-z'‖ := by
    rw [he]
    have ht := (norm_sub_le (z-z') (Matrix.toEuclideanCLM (𝕜 := ℝ) Q (z-z'))).trans
      (add_le_add le_rfl (hQ (z-z')))
    linarith
  have ht := dist_triangle (completedMatrixEndpoint P W u z)
    (completedMatrixEndpoint Q W' v z) (completedMatrixEndpoint Q W' v z')
  simp only [dist_eq_norm] at ht
  linarith

end SKConstants.GaussianProposal
