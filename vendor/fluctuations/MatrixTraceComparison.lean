module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have h := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h

theorem trace_hessian_covariance_le_square {H C : Matrix ι ι ℝ} {u : ℝ}
    (hH : H.PosSemidef) (hHC : (H - u • C).PosSemidef) :
    u * (H * C).trace ≤ (H * H).trace := by
  have h := trace_mul_nonneg_of_posSemidef hH hHC
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul] at h
  simp only [smul_eq_mul] at h
  linarith

theorem trace_covariance_square_le_hessian_square {H C : Matrix ι ι ℝ} {u : ℝ}
    (hu : 0 ≤ u) (hH : H.PosSemidef) (hC : C.PosSemidef)
    (hHC : (H - u • C).PosSemidef) :
    u ^ 2 * (C * C).trace ≤ (H * H).trace := by
  have hfirst := trace_hessian_covariance_le_square hH hHC
  have hsecond := trace_mul_nonneg_of_posSemidef hC hHC
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_mul_comm C H] at hsecond
  simp only [smul_eq_mul] at hsecond
  have hscaled := mul_nonneg hu hsecond
  nlinarith

theorem trace_hessian_covariance_le_div {H C : Matrix ι ι ℝ} {u : ℝ}
    (hu : 0 < u) (hH : H.PosSemidef) (hHC : (H - u • C).PosSemidef) :
    (H * C).trace ≤ (H * H).trace / u := by
  apply (le_div_iff₀ hu).mpr
  simpa only [mul_comm] using trace_hessian_covariance_le_square hH hHC

theorem trace_covariance_square_le_div {H C : Matrix ι ι ℝ} {u : ℝ}
    (hu : 0 < u) (hH : H.PosSemidef) (hC : C.PosSemidef)
    (hHC : (H - u • C).PosSemidef) :
    (C * C).trace ≤ (H * H).trace / u ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hu)).mpr
  simpa only [mul_comm] using trace_covariance_square_le_hessian_square hu.le hH hC hHC

theorem posSemidef_entry_squares_le_trace_square {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) : (∑ i, ∑ j, (A i j)^2) ≤ A.trace^2 := by
  classical
  let R := CFC.sqrt A
  have hs : R.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have he : A = R * R := (CFC.sqrt_mul_sqrt_self A hA.nonneg).symm
  have hgram (i j : ι) : A i j = ∑ k, R i k * R j k := by
    rw [he, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    have hsym : R k j = R j k := by simpa only [star_trivial] using hs.apply j k
    rw [hsym]
  have hentry (i j : ι) : (A i j)^2 ≤ A i i * A j j := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => R i k) (fun k => R j k)
    rw [← hgram i j] at h
    have hdiag (k : ι) : (∑ z, (R k z)^2) = A k k := by
      rw [hgram k k]
      simp only [pow_two]
    rw [hdiag i, hdiag j] at h
    exact h
  calc
    _ ≤ ∑ i, ∑ j, A i i * A j j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = A.trace^2 := by
      simp only [Matrix.trace, Matrix.diag, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

theorem posSemidef_entry_squares_le_one {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (htrace : A.trace ≤ 1) : (∑ i, ∑ j, (A i j)^2) ≤ 1 := by
  have h := posSemidef_entry_squares_le_trace_square hA
  have h0 := hA.trace_nonneg
  nlinarith

end OAI.SKFluctuations
