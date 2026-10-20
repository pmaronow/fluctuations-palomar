module

public import SKConstants.Completion.LC5.Energy
public import SKConstants.EmpiricalCovariance
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.LGram
open LC5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d k N : ℕ}

def coordinateLift (e : Fin k → Fin d) (a : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ i, a i • EuclideanSpace.single (e i) 1

theorem coordinateLift_norm (e : Fin k → Fin d) (he : Function.Injective e)
    (a : EuclideanSpace ℝ (Fin k)) : ‖coordinateLift e a‖ = ‖a‖ := by
  have ho := (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).comp e he
  have h := ho.inner_sum (fun i => a i) (fun i => a i) Finset.univ
  change inner (𝕜 := ℝ) (coordinateLift e a) (coordinateLift e a) = _ at h
  rw [real_inner_self_eq_norm_sq] at h
  simp only [RCLike.conj_to_real, ← pow_two] at h
  rw [← EuclideanSpace.real_norm_sq_eq] at h
  nlinarith [norm_nonneg (coordinateLift e a), norm_nonneg a]

theorem coordinateLift_inner (e : Fin k → Fin d)
    (a : EuclideanSpace ℝ (Fin k)) (x : EuclideanSpace ℝ (Fin d)) :
    inner (𝕜 := ℝ) (coordinateLift e a) x = ∑ i, a i * x (e i) := by
  simp [coordinateLift, sum_inner, real_inner_smul_left, EuclideanSpace.inner_single_left]

theorem coordinateBlock_inner (D : Matrix (Fin d) (Fin d) ℝ)
    (e f : Fin k → Fin d) (a b : EuclideanSpace ℝ (Fin k)) :
    inner (𝕜 := ℝ) a (Matrix.toEuclideanCLM (𝕜 := ℝ) (D.submatrix e f) b) =
      inner (𝕜 := ℝ) (coordinateLift e a)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) D (coordinateLift f b)) := by
  rw [coordinateLift_inner]
  simp only [coordinateLift, map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply,
    smul_eq_mul, Matrix.inner_toEuclideanCLM, dotProduct, Matrix.mulVec,
    Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm]

theorem coordinateBlock_norm_le (D : Matrix (Fin d) (Fin d) ℝ)
    (e f : Fin k → Fin d) (he : Function.Injective e) (hf : Function.Injective f) :
    ‖D.submatrix e f‖ ≤ ‖D‖ := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (D.submatrix e f)‖ ≤ ‖D‖
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg D)
  intro x y hx hy
  rw [real_inner_comm, coordinateBlock_inner]
  have h := LC5.inner_matrix_abs_le D (coordinateLift e y) (coordinateLift f x)
  rw [coordinateLift_norm e he, coordinateLift_norm f hf, hx, hy] at h
  simpa using (le_abs_self _).trans h

theorem coordinateColumn_norm_le (D : Matrix (Fin d) (Fin d) ℝ)
    (e : Fin k → Fin d) (he : Function.Injective e) (j : Fin d) :
    ‖WithLp.toLp 2 (fun i => D (e i) j)‖ ≤ ‖D‖ := by
  let v := WithLp.toLp 2 (fun i => D (e i) j)
  have hinner : inner (𝕜 := ℝ) v v =
      inner (𝕜 := ℝ) (coordinateLift e v)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) D (EuclideanSpace.single j 1)) := by
    rw [coordinateLift_inner, EuclideanSpace.inner_eq_star_dotProduct]
    simp [v, dotProduct, Matrix.mulVec, PiLp.single_apply]
  have h := LC5.inner_matrix_abs_le D (coordinateLift e v) (EuclideanSpace.single j 1)
  rw [← hinner, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _),
    coordinateLift_norm e he] at h
  simp only [PiLp.norm_single, norm_one, mul_one] at h
  change ‖v‖ ≤ ‖D‖
  nlinarith [norm_nonneg v, norm_nonneg D]

end SKConstants.Completion.LGram
