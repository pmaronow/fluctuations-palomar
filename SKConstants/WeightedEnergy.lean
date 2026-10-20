module

public import SKConstants.ConcreteCholesky
public import SKConstants.DyadicVectorBound
public import SKConstants.DyadicScalarBound
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

theorem inverse_transpose_perturbation_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (hunit : IsUnit C) (hsmall : ‖C - 1‖ ≤ 1 / 2) :
    ‖C.transpose⁻¹‖ ≤ 2 := by
  let U := C - 1
  let B := C.transpose⁻¹
  have hdet : IsUnit C.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp hunit
  have hBC : B * C.transpose = 1 := Matrix.nonsing_inv_mul C.transpose hdet
  have hC : C.transpose = 1 + U.transpose := by
    dsimp [U]
    simp only [Matrix.transpose_sub, Matrix.transpose_one]
    abel
  have hB : B = 1 - B * U.transpose := by
    rw [hC, mul_add, mul_one] at hBC
    rw [← hBC]
    abel
  have hone : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    norm_num
  have hn : ‖B‖ ≤ 1 + ‖B‖ * ‖U‖ := by
    calc
      _ = ‖1 - B * U.transpose‖ := congrArg norm hB
      _ ≤ ‖(1 : Matrix ι ι ℝ)‖ + ‖B * U.transpose‖ := norm_sub_le _ _
      _ ≤ 1 + ‖B‖ * ‖U.transpose‖ := add_le_add hone (norm_mul_le _ _)
      _ = _ := by rw [matrix_transpose_opNorm]
  have hm := mul_le_mul_of_nonneg_left hsmall (norm_nonneg B)
  dsimp [U] at hn
  change ‖B‖ ≤ 2
  nlinarith

theorem cholesky_coefficient_error_le (r : ℕ) (ε W : ℝ)
    (E C : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s eq : EuclideanSpace ℝ (Fin (2 ^ r)))
    (_hε : 0 ≤ ε) (hW : 0 ≤ W) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hupper : ∀ i j, j < i → C i j = 0) (hgram : C.transpose * C = 1 + E)
    (hunit : IsUnit C) (hU : ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε)
    (hq : ‖eq‖ ≤ W)
    (hL : dyadicMatrixSeminorm r s (halfUpperTruncation E) ≤ W)
    (hLt : dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose ≤ W) :
    ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) C.transpose⁻¹ (s + eq) - s‖ ≤ 6 * W := by
  let d : ℝ := (r + 1 : ℕ)
  let U := C - 1
  let L := halfUpperTruncation E
  let R := halfUpperTruncation (U.transpose * U)
  let B := C.transpose⁻¹
  let T := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hUp : ∀ i j, j < i → U i j = 0 := by
    intro i j hij
    simp [U, Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hij), hupper i j hij]
  have hrec := upper_factor_gram_recursion U hUp
  have hC : 1 + U = C := by dsimp [U]; abel
  rw [hC, hgram, add_sub_cancel_left] at hrec
  change U = L - R at hrec
  have hscaled := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * d by positivity)
  have hc : 2 * d * ‖U‖ ≤ 1 / 2 := by dsimp [U, d] at *; nlinarith
  have hrecstar : U = halfUpperTruncation E - halfUpperTruncation (star U * U) := by
    simpa only [L, R, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hrec
  have hp := dyadic_halfUpper_gram_le r U U s
  have hpstar : dyadicMatrixSeminorm r s (halfUpperTruncation (star U * U)) ≤
      2 * d * ‖U‖ * dyadicMatrixSeminorm r s U := by
    simpa only [d, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hp
  have hclosure := (weighted_cholesky_closure d U E halfUpperTruncation (dyadicMatrixSeminorm r s)
    hd hc hrecstar hpstar).1
  have hP : dyadicMatrixSeminorm r s U ≤ 2 * W := hclosure.trans (by linarith)
  have hsqrtd : Real.sqrt d ≤ d := Real.sqrt_le_iff.mpr ⟨hd, by nlinarith⟩
  have hR0 := dyadic_halfUpper_gram_transpose_root_le r U U s
  have hR : ‖T R.transpose s‖ ≤ W := by
    have hm := mul_le_mul_of_nonneg_right hsqrtd
      (mul_nonneg (norm_nonneg U) (apply_nonneg (dyadicMatrixSeminorm r s) U))
    have hh := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2 * d * ‖U‖ by positivity)
    have hk := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2 * W by positivity)
    change ‖T R.transpose s‖ ≤ W
    calc
      _ ≤ 2 * Real.sqrt d * ‖U‖ * dyadicMatrixSeminorm r s U := hR0
      _ ≤ 2 * d * ‖U‖ * dyadicMatrixSeminorm r s U := by nlinarith
      _ ≤ (2 * d * ‖U‖) * (2 * W) := hh
      _ ≤ W := by nlinarith
  have hUts : ‖T U.transpose s‖ ≤ 2 * W := by
    have hLt0 := dyadic_root_image_norm_le r L.transpose s
    have huT : U.transpose = L.transpose - R.transpose := by rw [hrec, Matrix.transpose_sub]
    rw [huT, map_sub, sub_apply]
    exact (norm_sub_le _ _).trans ((add_le_add (hLt0.trans hLt) hR).trans (by ring_nf; rfl))
  have hUn : ‖U‖ ≤ 1 / 2 := by
    have hn := norm_nonneg U
    nlinarith
  have hBn : ‖B‖ ≤ 2 := inverse_transpose_perturbation_norm_le C hunit hUn
  have hdet : IsUnit C.transpose.det := by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det C).mp hunit
  have hBC : B * C.transpose = 1 := Matrix.nonsing_inv_mul C.transpose hdet
  have hCt : C.transpose = 1 + U.transpose := by rw [← hC, Matrix.transpose_add, Matrix.transpose_one]
  have hBs : T B s + T B (T U.transpose s) = s := by
    have hone : (1 : EuclideanSpace ℝ (Fin (2 ^ r)) →L[ℝ] EuclideanSpace ℝ (Fin (2 ^ r))) s = s := rfl
    have hbs0 : T B (T C.transpose s) = s := by
      calc
        _ = T (B * C.transpose) s := by rw [map_mul, mul_apply_eq_comp]
        _ = T (1 : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) s := by rw [hBC]
        _ = s := by rw [map_one]; rfl
    simpa only [hCt, map_add, add_apply, map_one, hone] using hbs0
  have hbsub : T B s - s = -T B (T U.transpose s) := by
    calc
      _ = T B s - (T B s + T B (T U.transpose s)) :=
        congrArg (fun x => T B s - x) hBs.symm
      _ = _ := by abel
  have hdiff : T B (s + eq) - s = T B (eq - T U.transpose s) := by
    simp only [map_add, map_sub]
    calc
      _ = (T B s - s) + T B eq := by abel
      _ = _ := by rw [hbsub]; abel
  change ‖T B (s + eq) - s‖ ≤ 6 * W
  rw [hdiff]
  calc
    _ ≤ ‖B‖ * ‖eq - T U.transpose s‖ := by simpa only [T, Matrix.l2_opNorm_toEuclideanCLM] using (T B).le_opNorm _
    _ ≤ 2 * (‖eq‖ + ‖T U.transpose s‖) := mul_le_mul hBn (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ _ := by linarith

theorem upper_cholesky_weighted_closure_le (r : ℕ) (ε : ℝ)
    (E C : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hupper : ∀ i j, j < i → C i j = 0) (hgram : C.transpose * C = 1 + E)
    (hU : ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε)
    (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    dyadicMatrixSeminorm r w (C - 1) ≤ 2 * dyadicMatrixSeminorm r w (halfUpperTruncation E) := by
  let d : ℝ := (r + 1 : ℕ)
  let U := C - 1
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hUp : ∀ i j, j < i → U i j = 0 := by
    intro i j hij
    simp [U, Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hij), hupper i j hij]
  have hrec := upper_factor_gram_recursion U hUp
  have hC : 1 + U = C := by dsimp [U]; abel
  rw [hC, hgram, add_sub_cancel_left] at hrec
  have hscaled := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * d by positivity)
  have hc : 2 * d * ‖U‖ ≤ 1 / 2 := by dsimp [U, d] at *; nlinarith
  have hrecstar : U = halfUpperTruncation E - halfUpperTruncation (star U * U) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hrec
  have hp := dyadic_halfUpper_gram_le r U U w
  have hpstar : dyadicMatrixSeminorm r w (halfUpperTruncation (star U * U)) ≤
      2 * d * ‖U‖ * dyadicMatrixSeminorm r w U := by
    simpa only [d, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hp
  exact (weighted_cholesky_closure d U E halfUpperTruncation (dyadicMatrixSeminorm r w)
    hd hc hrecstar hpstar).1

theorem pairing_remainder_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U L R : Matrix ι ι ℝ) (s u eq b ev : EuclideanSpace ℝ ι)
    (hrec : U = L - R)
    (hcoeff : u = eq - Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) U.transpose (s + u)) :
    inner (𝕜 := ℝ) (s + u) (b + ev) - inner (𝕜 := ℝ) s b -
      (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) L b) + inner (𝕜 := ℝ) s ev) =
      inner (𝕜 := ℝ) s (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) R b) -
        inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) U b) u + inner (𝕜 := ℝ) u ev := by
  have hc := congrArg (fun v => inner (𝕜 := ℝ) v b) hcoeff
  rw [hrec, Matrix.transpose_sub, map_sub, sub_apply, map_add] at hc
  simp only [inner_sub_left, inner_add_left, matrix_transpose_inner] at hc
  rw [real_inner_comm u (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) U b)]
  rw [hrec, map_sub, sub_apply, inner_sub_right]
  simp only [inner_add_left, inner_add_right]
  linarith

theorem upper_inverse_isUpper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (C : Matrix ι ι ℝ) (hunit : IsUnit C)
    (hupper : ∀ i j, j < i → C i j = 0) :
    ∀ i j, j < i → C⁻¹ i j = 0 := by
  let _ := hunit.invertible
  have hu : C.IsUpperTriangular := fun {i j} h => hupper i j h
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hu
  exact fun i j h => hi h

theorem inverse_transpose_times_strictLower_fullUpper_eq_zero
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (C H : Matrix ι ι ℝ) (hunit : IsUnit C)
    (hupper : ∀ i j, j < i → C i j = 0)
    (hH : ∀ i j, i ≤ j → H i j = 0) :
    fullUpperTruncation (C.transpose⁻¹ * H) = 0 := by
  have hi := upper_inverse_isUpper C hunit hupper
  rw [← Matrix.transpose_nonsing_inv]
  ext i j
  by_cases hij : i ≤ j
  · simp only [fullUpperTruncation, hij, ite_true, Matrix.zero_apply, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k ≤ i
    · rw [hH k j (le_trans hk hij)]
      simp
    · simp [Matrix.transpose_apply, hi k i (lt_of_not_ge hk)]
  · simp [fullUpperTruncation, hij]

theorem cholesky_pairing_remainder_le (r : ℕ) (ε W : ℝ)
    (E C : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2 ^ r)))
    (hε : 0 ≤ ε) (hW : 0 ≤ W) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hupper : ∀ i j, j < i → C i j = 0) (hgram : C.transpose * C = 1 + E)
    (hunit : IsUnit C) (hU : ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε)
    (hq : ‖eq‖ ≤ W) (hv : ‖ev‖ ≤ W)
    (hLs : dyadicMatrixSeminorm r s (halfUpperTruncation E) ≤ W)
    (hLts : dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose ≤ W)
    (hLb : dyadicMatrixSeminorm r b (halfUpperTruncation E) ≤ W) :
    let c := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) C.transpose⁻¹ (s + eq)
    |inner (𝕜 := ℝ) c (b + ev) - inner (𝕜 := ℝ) s b -
      (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s
        (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (halfUpperTruncation E) b) +
        inner (𝕜 := ℝ) s ev)| ≤ 26 * W ^ 2 := by
  let U := C - 1
  let L := halfUpperTruncation E
  let R := halfUpperTruncation (U.transpose * U)
  let T := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
  let c := T C.transpose⁻¹ (s + eq)
  let u := c - s
  have hcu : s + u = c := by dsimp [u]; abel
  have hup : ∀ i j, j < i → U i j = 0 := by
    intro i j hij
    simp [U, Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hij), hupper i j hij]
  have hrec := upper_factor_gram_recursion U hup
  have hC : 1 + U = C := by dsimp [U]; abel
  rw [hC, hgram, add_sub_cancel_left] at hrec
  change U = L - R at hrec
  have hdet : IsUnit C.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp hunit
  have hCB : C.transpose * C.transpose⁻¹ = 1 := Matrix.mul_nonsing_inv C.transpose hdet
  have hqvec : T C.transpose c = s + eq := by
    change T C.transpose (T C.transpose⁻¹ (s + eq)) = s + eq
    rw [← mul_apply_eq_comp, ← map_mul, hCB, map_one]
    rfl
  have hqvec' : c + T U.transpose c = s + eq := by
    have hCt : C.transpose = 1 + U.transpose := by rw [← hC, Matrix.transpose_add, Matrix.transpose_one]
    rw [hCt, map_add, add_apply, map_one] at hqvec
    exact hqvec
  have hcoeff : u = eq - T U.transpose (s + u) := by
    rw [hcu]
    have hc : c = s + eq - T U.transpose c := eq_sub_iff_add_eq.mpr hqvec'
    calc
      _ = (s + eq - T U.transpose c) - s := congrArg (fun x => x - s) hc
      _ = _ := by abel
  have hid := pairing_remainder_identity U L R s u eq b ev hrec hcoeff
  rw [hcu] at hid
  have hus : dyadicMatrixSeminorm r s U ≤ 2 * W :=
    (upper_cholesky_weighted_closure_le r ε E C hsmall hupper hgram hU s).trans (by linarith)
  have hub : dyadicMatrixSeminorm r b U ≤ 2 * W :=
    (upper_cholesky_weighted_closure_le r ε E C hsmall hupper hgram hU b).trans (by linarith)
  have hun : ‖u‖ ≤ 6 * W := cholesky_coefficient_error_le r ε W E C s eq
    hε hW hsmall hupper hgram hunit hU hq hLs hLts
  have hR : |inner (𝕜 := ℝ) s (T R b)| ≤ 8 * W ^ 2 := by
    have hh := dyadic_halfUpper_gram_bilinear_le r U U s b
    have hm := mul_le_mul hus hub (apply_nonneg _ _) (by positivity : 0 ≤ 2 * W)
    change |inner (𝕜 := ℝ) s (T R b)| ≤ 8 * W ^ 2
    nlinarith
  have hUu : |inner (𝕜 := ℝ) (T U b) u| ≤ 12 * W ^ 2 := by
    have hn : ‖T U b‖ ≤ 2 * W := (dyadic_root_image_norm_le r U b).trans hub
    have hm := mul_le_mul hn hun (norm_nonneg u) (by positivity : 0 ≤ 2 * W)
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith)
  have huev : |inner (𝕜 := ℝ) u ev| ≤ 6 * W ^ 2 := by
    have hm := mul_le_mul hun hv (norm_nonneg ev) (by positivity : 0 ≤ 6 * W)
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith)
  change |inner (𝕜 := ℝ) c (b + ev) - inner (𝕜 := ℝ) s b -
    (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s (T L b) + inner (𝕜 := ℝ) s ev)| ≤ _
  rw [hid]
  have hsub : |inner (𝕜 := ℝ) s (T R b) - inner (𝕜 := ℝ) (T U b) u| ≤
      |inner (𝕜 := ℝ) s (T R b)| + |inner (𝕜 := ℝ) (T U b) u| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (inner (𝕜 := ℝ) s (T R b)) 0 (inner (𝕜 := ℝ) (T U b) u)
  exact (abs_add_le _ _).trans ((add_le_add hsub (le_refl _)).trans
    ((add_le_add (add_le_add hR hUu) huev).trans (by ring_nf; rfl)))

theorem fullUpper_weighted_cross_remainder_le (r : ℕ) (ε W : ℝ)
    (H : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s u : EuclideanSpace ℝ (Fin (2 ^ r)))
    (hε : 0 ≤ ε) (hW : 0 ≤ W) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hH : ‖H‖ ≤ ε) (hu : ‖u‖ ≤ 6 * W)
    (hHs : dyadicMatrixSeminorm r s H ≤ W)
    (hHts : dyadicMatrixSeminorm r s H.transpose ≤ W) :
    |inner (𝕜 := ℝ) (s + u)
      (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (fullUpperTruncation H) (s + u)) -
      inner (𝕜 := ℝ) s
        (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (fullUpperTruncation H) s)| ≤
      (24 * Real.sqrt (r + 1 : ℕ) + 36) * W ^ 2 := by
  let d : ℝ := (r + 1 : ℕ)
  let T := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
  let G := fullUpperTruncation H
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hde : d * ε ≤ 1 := by
    have hh : d ≤ d ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh hε
    dsimp [d] at *
    nlinarith
  have hone : ‖(1 : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)‖ = 1 := norm_one
  have hNu : dyadicMatrixSeminorm r u 1 ≤ 6 * Real.sqrt d * W := by
    have hh := dyadicMatrixSeminorm_le r u 1
    rw [hone, mul_one] at hh
    have hm := mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg d)
    change dyadicMatrixSeminorm r u 1 ≤ 6 * Real.sqrt d * W
    nlinarith
  have hA : |inner (𝕜 := ℝ) u (T G s)| ≤ 12 * Real.sqrt d * W ^ 2 := by
    have hh := dyadic_fullUpper_gram_bilinear_le r 1 H u s
    simp only [Matrix.transpose_one, one_mul] at hh
    have hm := mul_le_mul hNu hHs (apply_nonneg _ _) (by positivity : 0 ≤ 6 * Real.sqrt d * W)
    change |inner (𝕜 := ℝ) u (T G s)| ≤ 12 * Real.sqrt d * W ^ 2
    nlinarith
  have hB : |inner (𝕜 := ℝ) s (T G u)| ≤ 12 * Real.sqrt d * W ^ 2 := by
    have hh := dyadic_fullUpper_gram_bilinear_le r H.transpose 1 s u
    simp only [Matrix.transpose_transpose, mul_one] at hh
    have hm := mul_le_mul hHts hNu (apply_nonneg _ _) hW
    change |inner (𝕜 := ℝ) s (T G u)| ≤ 12 * Real.sqrt d * W ^ 2
    nlinarith
  have hGn : ‖G‖ ≤ d * ε :=
    (fullUpperTruncation_opNorm_le r H).trans (mul_le_mul_of_nonneg_left hH (by positivity))
  have hC : |inner (𝕜 := ℝ) u (T G u)| ≤ 36 * W ^ 2 := by
    have ht : ‖T G u‖ ≤ d * ε * ‖u‖ := by
      calc
        _ ≤ ‖G‖ * ‖u‖ := by simpa only [T, Matrix.l2_opNorm_toEuclideanCLM] using (T G).le_opNorm u
        _ ≤ _ := mul_le_mul_of_nonneg_right hGn (norm_nonneg u)
    have hm := mul_le_mul_of_nonneg_left ht (norm_nonneg u)
    have hsq := (sq_le_sq₀ (norm_nonneg u) (by positivity : 0 ≤ 6 * W)).2 hu
    have hsq' := mul_le_mul_of_nonneg_left hsq (show 0 ≤ d * ε by positivity)
    have hfinal := mul_le_mul_of_nonneg_right hde (sq_nonneg W)
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith)
  have heq : inner (𝕜 := ℝ) (s + u) (T G (s + u)) - inner (𝕜 := ℝ) s (T G s) =
      inner (𝕜 := ℝ) u (T G s) + inner (𝕜 := ℝ) s (T G u) + inner (𝕜 := ℝ) u (T G u) := by
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  change |inner (𝕜 := ℝ) (s + u) (T G (s + u)) - inner (𝕜 := ℝ) s (T G s)| ≤
    (24 * Real.sqrt d + 36) * W ^ 2
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) (le_refl _)).trans
    ((add_le_add (add_le_add hA hB) hC).trans (by ring_nf; rfl)))

theorem inverse_product_weighted_remainder_le (r : ℕ) (ε W : ℝ)
    (C H : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s u : EuclideanSpace ℝ (Fin (2 ^ r)))
    (hε : 0 ≤ ε) (hW : 0 ≤ W) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hunit : IsUnit C) (hU : ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε)
    (hUs : dyadicMatrixSeminorm r s (C - 1) ≤ 2 * W)
    (hH : ‖H‖ ≤ ε) (hHs : dyadicMatrixSeminorm r s H ≤ W)
    (hu : ‖u‖ ≤ 6 * W) :
    |inner (𝕜 := ℝ) (s + u)
      (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
        (fullUpperTruncation ((C.transpose⁻¹ - 1) * H)) (s + u))| ≤ 98 * W ^ 2 := by
  let d : ℝ := (r + 1 : ℕ)
  let U := C - 1
  let B := C.transpose⁻¹
  let F := B - 1
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hsqrt : Real.sqrt d ≤ d := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hscaled : 16 * d ^ 2 * ε ≤ 1 := hsmall
  have hUn : ‖U‖ ≤ 1 / 2 := by
    have hh : d ≤ d ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hh hε
    change ‖U‖ ≤ 1 / 2
    dsimp [U, d] at *
    nlinarith
  have hBn : ‖B‖ ≤ 2 := inverse_transpose_perturbation_norm_le C hunit hUn
  have hdet : IsUnit C.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det C).mp hunit
  have hCB : C.transpose * B = 1 := Matrix.mul_nonsing_inv C.transpose hdet
  have hBtC : B.transpose * C = 1 := by
    have hh := congrArg Matrix.transpose hCB
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using hh
  have hC : C = 1 + U := by dsimp [U]; abel
  have hFt : F.transpose = -(B.transpose * U) := by
    have hh : B.transpose + B.transpose * U = 1 := by
      simpa only [hC, mul_add, mul_one] using hBtC
    calc
      _ = B.transpose - 1 := by simp only [F, Matrix.transpose_sub, Matrix.transpose_one]
      _ = B.transpose - (B.transpose + B.transpose * U) := congrArg (fun x => B.transpose - x) hh.symm
      _ = _ := by abel
  have hFn : ‖F‖ ≤ 2 * ‖U‖ := by
    calc
      _ = ‖F.transpose‖ := (matrix_transpose_opNorm F).symm
      _ = ‖B.transpose * U‖ := by rw [hFt, norm_neg]
      _ ≤ ‖B.transpose‖ * ‖U‖ := norm_mul_le _ _
      _ ≤ _ := by rw [matrix_transpose_opNorm]; exact mul_le_mul_of_nonneg_right hBn (norm_nonneg U)
  have hNsF : dyadicMatrixSeminorm r s F.transpose ≤ 4 * W := by
    rw [hFt, map_neg_eq_map]
    have hh := dyadicMatrixSeminorm_mul_le r s B.transpose U
    rw [matrix_transpose_opNorm] at hh
    have hm := mul_le_mul hBn hUs (apply_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 2)
    exact hh.trans (by nlinarith)
  have hNuF : dyadicMatrixSeminorm r u F.transpose ≤ 3 * W := by
    have hh := dyadicMatrixSeminorm_le r u F.transpose
    rw [matrix_transpose_opNorm] at hh
    have hFn' : ‖F‖ ≤ 4 * d * ε := hFn.trans (by dsimp [U, d] at *; linarith)
    have hm := mul_le_mul hsqrt hFn' (norm_nonneg F) (by positivity : 0 ≤ d)
    have hm' := mul_le_mul hm hu (norm_nonneg u) (by positivity : 0 ≤ d * (4 * d * ε))
    have hk := mul_le_mul_of_nonneg_right hscaled hW
    exact hh.trans (by nlinarith)
  have hNcF : dyadicMatrixSeminorm r (s + u) F.transpose ≤ 7 * W :=
    (dyadicMatrixSeminorm_add_vector_le r s u F.transpose).trans (by linarith)
  have hNuH : dyadicMatrixSeminorm r u H ≤ 6 * W := by
    have hh := dyadicMatrixSeminorm_le r u H
    have hm := mul_le_mul hsqrt hH (norm_nonneg H) (by positivity : 0 ≤ d)
    have hm' := mul_le_mul hm hu (norm_nonneg u) (by positivity : 0 ≤ d * ε)
    have hde : d * ε ≤ 1 := by
      have hh : d ≤ d ^ 2 := by nlinarith
      have hk := mul_le_mul_of_nonneg_right hh hε
      nlinarith
    have hk := mul_le_mul_of_nonneg_right hde hW
    exact hh.trans (by nlinarith)
  have hNcH : dyadicMatrixSeminorm r (s + u) H ≤ 7 * W :=
    (dyadicMatrixSeminorm_add_vector_le r s u H).trans (by linarith)
  have hh := dyadic_fullUpper_gram_bilinear_le r F.transpose H (s + u) (s + u)
  simp only [Matrix.transpose_transpose] at hh
  have hm := mul_le_mul hNcF hNcH (apply_nonneg _ _) (by positivity : 0 ≤ 7 * W)
  change |inner (𝕜 := ℝ) (s + u)
    (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (fullUpperTruncation (F * H)) (s + u))| ≤ _
  exact hh.trans (by nlinarith)

theorem fullUpperTruncation_add {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A B : Matrix ι ι ℝ) :
    fullUpperTruncation (A + B) = fullUpperTruncation A + fullUpperTruncation B := by
  ext i j
  simp only [fullUpperTruncation, Matrix.add_apply]
  split_ifs <;> simp

theorem weighted_upper_cholesky_energy_bound (r : ℕ) (ε W : ℝ)
    (E C H₀ H : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2 ^ r)))
    (hε : 0 ≤ ε) (hW : 0 ≤ W) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hupper : ∀ i j, j < i → C i j = 0) (hgram : C.transpose * C = 1 + E)
    (hunit : IsUnit C) (hU : ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε)
    (hH₀ : ∀ i j, i ≤ j → H₀ i j = 0) (hH : ‖H‖ ≤ ε)
    (hq : ‖eq‖ ≤ W) (hv : ‖ev‖ ≤ W)
    (hLs : dyadicMatrixSeminorm r s (halfUpperTruncation E) ≤ W)
    (hLts : dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose ≤ W)
    (hLb : dyadicMatrixSeminorm r b (halfUpperTruncation E) ≤ W)
    (hHs : dyadicMatrixSeminorm r s H ≤ W)
    (hHts : dyadicMatrixSeminorm r s H.transpose ≤ W) :
    let T := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
    let c := T C.transpose⁻¹ (s + eq)
    |inner (𝕜 := ℝ) c (b + ev) -
      inner (𝕜 := ℝ) c (T (fullUpperTruncation (C.transpose⁻¹ * (H₀ + H))) c) -
      inner (𝕜 := ℝ) s b -
      (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s (T (halfUpperTruncation E) b) +
        inner (𝕜 := ℝ) s ev - inner (𝕜 := ℝ) s (T (fullUpperTruncation H) s))| ≤
      200 * (r + 1 : ℕ) * W ^ 2 := by
  let d : ℝ := (r + 1 : ℕ)
  let T := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
  let B := C.transpose⁻¹
  let F := B - 1
  let c := T B (s + eq)
  let u := c - s
  have hcu : s + u = c := by dsimp [u]; abel
  have hu : ‖u‖ ≤ 6 * W := cholesky_coefficient_error_le r ε W E C s eq
    hε hW hsmall hupper hgram hunit hU hq hLs hLts
  have hUs : dyadicMatrixSeminorm r s (C - 1) ≤ 2 * W :=
    (upper_cholesky_weighted_closure_le r ε E C hsmall hupper hgram hU s).trans (by linarith)
  have hp := cholesky_pairing_remainder_le r ε W E C s eq b ev hε hW hsmall
    hupper hgram hunit hU hq hv hLs hLts hLb
  have hx := fullUpper_weighted_cross_remainder_le r ε W H s u hε hW hsmall hH hu hHs hHts
  have hf := inverse_product_weighted_remainder_le r ε W C H s u hε hW hsmall
    hunit hU hUs hH hHs hu
  rw [hcu] at hx hf
  have hH0 : fullUpperTruncation (B * H₀) = 0 :=
    inverse_transpose_times_strictLower_fullUpper_eq_zero C H₀ hunit hupper hH₀
  have hBH : B * H = H + F * H := by dsimp [F]; noncomm_ring
  have hfull : fullUpperTruncation (B * (H₀ + H)) =
      fullUpperTruncation H + fullUpperTruncation (F * H) := by
    rw [mul_add, fullUpperTruncation_add, hH0, zero_add, hBH, fullUpperTruncation_add]
  let P := inner (𝕜 := ℝ) c (b + ev) - inner (𝕜 := ℝ) s b -
    (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s (T (halfUpperTruncation E) b) + inner (𝕜 := ℝ) s ev)
  let X := inner (𝕜 := ℝ) c (T (fullUpperTruncation H) c) -
    inner (𝕜 := ℝ) s (T (fullUpperTruncation H) s)
  let Z := inner (𝕜 := ℝ) c (T (fullUpperTruncation (F * H)) c)
  have hid : inner (𝕜 := ℝ) c (b + ev) -
      inner (𝕜 := ℝ) c (T (fullUpperTruncation (B * (H₀ + H))) c) - inner (𝕜 := ℝ) s b -
      (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s (T (halfUpperTruncation E) b) +
        inner (𝕜 := ℝ) s ev - inner (𝕜 := ℝ) s (T (fullUpperTruncation H) s)) = P - X - Z := by
    rw [hfull, map_add, add_apply, inner_add_right]
    dsimp [P, X, Z]
    simp only [inner_add_right]
    ring
  have hPX : |P - X| ≤ |P| + |X| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le P 0 X
  have hPZ : |P - X - Z| ≤ |P - X| + |Z| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (P - X) 0 Z
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hsqrt : Real.sqrt d ≤ d := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hnum : 26 + (24 * Real.sqrt d + 36) + 98 ≤ 200 * d := by nlinarith
  have hnumW := mul_le_mul_of_nonneg_right hnum (sq_nonneg W)
  change |inner (𝕜 := ℝ) c (b + ev) -
    inner (𝕜 := ℝ) c (T (fullUpperTruncation (B * (H₀ + H))) c) - inner (𝕜 := ℝ) s b -
    (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s (T (halfUpperTruncation E) b) +
      inner (𝕜 := ℝ) s ev - inner (𝕜 := ℝ) s (T (fullUpperTruncation H) s))| ≤ 200 * d * W ^ 2
  rw [hid]
  exact hPZ.trans ((add_le_add hPX (le_refl _)).trans
    ((add_le_add (add_le_add hp hx) hf).trans (by dsimp [d] at *; nlinarith)))

theorem exists_weighted_small_upper_cholesky (r : ℕ) (ε : ℝ)
    (E : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (hε : 0 ≤ ε) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hE : ‖E‖ ≤ ε) (hsym : E.transpose = E) :
    ∃ C : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ,
      (∀ i j, j < i → C i j = 0) ∧ (∀ i, 0 < C i i) ∧
      C.transpose * C = 1 + E ∧ IsUnit C ∧
      ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε ∧
      ∀ w : EuclideanSpace ℝ (Fin (2 ^ r)),
        dyadicMatrixSeminorm r w (C - 1) ≤ 2 * dyadicMatrixSeminorm r w (halfUpperTruncation E) ∧
        dyadicMatrixSeminorm r w (C - 1 - halfUpperTruncation E) ≤
          8 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε * dyadicMatrixSeminorm r w (halfUpperTruncation E) := by
  obtain ⟨C, hupper, hdiag, hgram, hunit, hU⟩ :=
    exists_small_upper_cholesky r ε E hε hsmall hE hsym
  refine ⟨C, hupper, hdiag, hgram, hunit, hU, ?_⟩
  intro w
  let d : ℝ := (r + 1 : ℕ)
  let U := C - 1
  let P := dyadicMatrixSeminorm r w
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hUp : ∀ i j, j < i → U i j = 0 := by
    intro i j hij
    simp [U, Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hij), hupper i j hij]
  have hrec := upper_factor_gram_recursion U hUp
  have hC : 1 + U = C := by dsimp [U]; abel
  rw [hC, hgram, add_sub_cancel_left] at hrec
  have hrecstar : U = halfUpperTruncation E - halfUpperTruncation (star U * U) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hrec
  have hscaled := mul_le_mul_of_nonneg_left hU (show 0 ≤ 2 * d by positivity)
  have hcoefficient : 2 * d * ‖U‖ ≤ 1 / 2 := by dsimp [U, d] at *; nlinarith
  have hproduct : P (halfUpperTruncation (star U * U)) ≤ 2 * d * ‖U‖ * P U := by
    simpa only [P, d, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      dyadic_halfUpper_gram_le r U U w
  obtain ⟨hclosure, hresidual⟩ := weighted_cholesky_closure d U E halfUpperTruncation P hd
    hcoefficient hrecstar hproduct
  refine ⟨hclosure, hresidual.trans ?_⟩
  have hscaled' := mul_le_mul_of_nonneg_left hU (show 0 ≤ 4 * d by positivity)
  have hm := mul_le_mul_of_nonneg_right hscaled' (apply_nonneg P (halfUpperTruncation E))
  convert hm using 1
  dsimp [U, d, P]
  ring

theorem exists_upper_cholesky_with_energy_bound (r : ℕ) (ε W : ℝ)
    (E H₀ H : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2 ^ r)))
    (hε : 0 ≤ ε) (hW : 0 ≤ W) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hE : ‖E‖ ≤ ε) (hsym : E.transpose = E)
    (hH₀ : ∀ i j, i ≤ j → H₀ i j = 0) (hH : ‖H‖ ≤ ε)
    (hq : ‖eq‖ ≤ W) (hv : ‖ev‖ ≤ W)
    (hLs : dyadicMatrixSeminorm r s (halfUpperTruncation E) ≤ W)
    (hLts : dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose ≤ W)
    (hLb : dyadicMatrixSeminorm r b (halfUpperTruncation E) ≤ W)
    (hHs : dyadicMatrixSeminorm r s H ≤ W)
    (hHts : dyadicMatrixSeminorm r s H.transpose ≤ W) :
    ∃ C : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ,
      (∀ i j, j < i → C i j = 0) ∧ (∀ i, 0 < C i i) ∧
      C.transpose * C = 1 + E ∧ IsUnit C ∧ ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε ∧
      let T := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      let c := T C.transpose⁻¹ (s + eq)
      ‖c - s‖ ≤ 6 * W ∧
      |inner (𝕜 := ℝ) c (b + ev) -
        inner (𝕜 := ℝ) c (T (fullUpperTruncation (C.transpose⁻¹ * (H₀ + H))) c) -
        inner (𝕜 := ℝ) s b -
        (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s (T (halfUpperTruncation E) b) +
          inner (𝕜 := ℝ) s ev - inner (𝕜 := ℝ) s (T (fullUpperTruncation H) s))| ≤
        200 * (r + 1 : ℕ) * W ^ 2 := by
  obtain ⟨C, hupper, hdiag, hgram, hunit, hU⟩ :=
    exists_small_upper_cholesky r ε E hε hsmall hE hsym
  refine ⟨C, hupper, hdiag, hgram, hunit, hU, ?_, ?_⟩
  · exact cholesky_coefficient_error_le r ε W E C s eq hε hW hsmall
      hupper hgram hunit hU hq hLs hLts
  · exact weighted_upper_cholesky_energy_bound r ε W E C H₀ H s eq b ev
      hε hW hsmall hupper hgram hunit hU hH₀ hH hq hv hLs hLts hLb hHs hHts

theorem exists_upper_cholesky_with_quadratic_energy_bound (r : ℕ) (ε : ℝ)
    (E H₀ H : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2 ^ r)))
    (hε : 0 ≤ ε) (hsmall : 16 * ((r + 1 : ℕ) : ℝ) ^ 2 * ε ≤ 1)
    (hE : ‖E‖ ≤ ε) (hsym : E.transpose = E)
    (hH₀ : ∀ i j, i ≤ j → H₀ i j = 0) (hH : ‖H‖ ≤ ε) :
    let Q := ‖eq‖ ^ 2 + ‖ev‖ ^ 2 +
      dyadicMatrixSeminorm r s (halfUpperTruncation E) ^ 2 +
      dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose ^ 2 +
      dyadicMatrixSeminorm r b (halfUpperTruncation E) ^ 2 +
      dyadicMatrixSeminorm r s H ^ 2 + dyadicMatrixSeminorm r s H.transpose ^ 2
    ∃ C : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ,
      (∀ i j, j < i → C i j = 0) ∧ (∀ i, 0 < C i i) ∧
      C.transpose * C = 1 + E ∧ IsUnit C ∧ ‖C - 1‖ ≤ 2 * (r + 1 : ℕ) * ε ∧
      let T := Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
      let c := T C.transpose⁻¹ (s + eq)
      ‖c - s‖ ≤ 6 * Real.sqrt Q ∧
      |inner (𝕜 := ℝ) c (b + ev) -
        inner (𝕜 := ℝ) c (T (fullUpperTruncation (C.transpose⁻¹ * (H₀ + H))) c) -
        inner (𝕜 := ℝ) s b -
        (inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s (T (halfUpperTruncation E) b) +
          inner (𝕜 := ℝ) s ev - inner (𝕜 := ℝ) s (T (fullUpperTruncation H) s))| ≤
        200 * (r + 1 : ℕ) * Q := by
  let Q := ‖eq‖ ^ 2 + ‖ev‖ ^ 2 +
    dyadicMatrixSeminorm r s (halfUpperTruncation E) ^ 2 +
    dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose ^ 2 +
    dyadicMatrixSeminorm r b (halfUpperTruncation E) ^ 2 +
    dyadicMatrixSeminorm r s H ^ 2 + dyadicMatrixSeminorm r s H.transpose ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hcomp (x : ℝ) (hx : 0 ≤ x) (hsq : x ^ 2 ≤ Q) : x ≤ Real.sqrt Q := by
    apply (sq_le_sq₀ hx (Real.sqrt_nonneg Q)).mp
    rwa [Real.sq_sqrt hQ]
  have hq : ‖eq‖ ≤ Real.sqrt Q := hcomp _ (norm_nonneg _) (by
    dsimp [Q]
    nlinarith only [sq_nonneg ‖ev‖,
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose),
      sq_nonneg (dyadicMatrixSeminorm r b (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s H),
      sq_nonneg (dyadicMatrixSeminorm r s H.transpose)])
  have hv : ‖ev‖ ≤ Real.sqrt Q := hcomp _ (norm_nonneg _) (by
    dsimp [Q]
    nlinarith only [sq_nonneg ‖eq‖,
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose),
      sq_nonneg (dyadicMatrixSeminorm r b (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s H),
      sq_nonneg (dyadicMatrixSeminorm r s H.transpose)])
  have hLs : (dyadicMatrixSeminorm r s (halfUpperTruncation E)) ≤ Real.sqrt Q := hcomp _ (apply_nonneg _ _) (by
    dsimp [Q]
    nlinarith only [sq_nonneg ‖eq‖,
      sq_nonneg ‖ev‖,
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose),
      sq_nonneg (dyadicMatrixSeminorm r b (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s H),
      sq_nonneg (dyadicMatrixSeminorm r s H.transpose)])
  have hLts : (dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose) ≤ Real.sqrt Q := hcomp _ (apply_nonneg _ _) (by
    dsimp [Q]
    nlinarith only [sq_nonneg ‖eq‖,
      sq_nonneg ‖ev‖,
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r b (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s H),
      sq_nonneg (dyadicMatrixSeminorm r s H.transpose)])
  have hLb : (dyadicMatrixSeminorm r b (halfUpperTruncation E)) ≤ Real.sqrt Q := hcomp _ (apply_nonneg _ _) (by
    dsimp [Q]
    nlinarith only [sq_nonneg ‖eq‖,
      sq_nonneg ‖ev‖,
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose),
      sq_nonneg (dyadicMatrixSeminorm r s H),
      sq_nonneg (dyadicMatrixSeminorm r s H.transpose)])
  have hHs : (dyadicMatrixSeminorm r s H) ≤ Real.sqrt Q := hcomp _ (apply_nonneg _ _) (by
    dsimp [Q]
    nlinarith only [sq_nonneg ‖eq‖,
      sq_nonneg ‖ev‖,
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose),
      sq_nonneg (dyadicMatrixSeminorm r b (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s H.transpose)])
  have hHts : (dyadicMatrixSeminorm r s H.transpose) ≤ Real.sqrt Q := hcomp _ (apply_nonneg _ _) (by
    dsimp [Q]
    nlinarith only [sq_nonneg ‖eq‖,
      sq_nonneg ‖ev‖,
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s (halfUpperTruncation E).transpose),
      sq_nonneg (dyadicMatrixSeminorm r b (halfUpperTruncation E)),
      sq_nonneg (dyadicMatrixSeminorm r s H)])
  obtain ⟨C, hupper, hdiag, hgram, hunit, hU, hc, hf⟩ :=
    exists_upper_cholesky_with_energy_bound r ε (Real.sqrt Q) E H₀ H s eq b ev hε
      (Real.sqrt_nonneg Q) hsmall hE hsym hH₀ hH hq hv hLs hLts hLb hHs hHts
  refine ⟨C, hupper, hdiag, hgram, hunit, hU, hc, ?_⟩
  simpa only [Real.sq_sqrt hQ] using hf

end SKConstants
