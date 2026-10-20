module

public import SKConstants.WeightedEnergy
import Mathlib.Tactic

@[expose] public section
noncomputable section

namespace SKConstants.Completion.LC5

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

def queryEnergyNormalForm {k : ℕ} (C H : Matrix (Fin k) (Fin k) ℝ)
    (q v : EuclideanSpace ℝ (Fin k)) : ℝ :=
  let T := Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)
  let c := T C.transpose⁻¹ q
  inner (𝕜 := ℝ) c v -
    inner (𝕜 := ℝ) c (T (fullUpperTruncation (C.transpose⁻¹ * H)) c)

def queryError (R : ℕ) (η : ℝ) : ℝ :=
  (2 * (R : ℝ) + 4) * η + 1400 * ((R + 1 : ℕ) : ℝ)^4 * η^2

theorem dyadic_sq_le_of_operator_bound (R : ℕ)
    (A : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (w : EuclideanSpace ℝ (Fin (2^R))) (a : ℝ)
    (ha : 0 ≤ a) (hA : ‖A‖ ≤ a) (hw : ‖w‖ ≤ 1) :
    dyadicMatrixSeminorm R w A ^ 2 ≤ ((R+1 : ℕ) : ℝ) * a^2 := by
  have h := dyadicMatrixSeminorm_le R w A
  have hm : Real.sqrt (R+1 : ℕ) * ‖A‖ * ‖w‖ ≤
      Real.sqrt (R+1 : ℕ) * a := by
    calc
      _ ≤ Real.sqrt (R+1 : ℕ) * a * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)) hw
          (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ha)
      _ = _ := mul_one _
  have hs := (sq_le_sq₀ (apply_nonneg _ _)
    (mul_nonneg (Real.sqrt_nonneg _) ha)).2 (h.trans hm)
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (R+1))] using hs

theorem inner_matrix_abs_le {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (x y : EuclideanSpace ℝ (Fin k)) :
    |inner (𝕜 := ℝ) x (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A y)| ≤
      ‖x‖ * ‖A‖ * ‖y‖ := by
  calc
    _ ≤ ‖x‖ * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A y‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖y‖) := mul_le_mul_of_nonneg_left
      (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) A).le_opNorm y) (norm_nonneg _)
    _ = _ := by ring

theorem exists_upper_cholesky_energy_of_operator_errors
    (R : ℕ) (η : ℝ)
    (EA H0 EH : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2^R)))
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖EA‖ ≤ η) (hsym : EA.transpose = EA)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖EH‖ ≤ η) (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∃ C : Matrix (Fin (2^R)) (Fin (2^R)) ℝ,
      (∀ i j, j < i → C i j = 0) ∧ (∀ i, 0 < C i i) ∧
      C.transpose * C = 1 + EA ∧ IsUnit C ∧
      |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b| ≤
        queryError R η := by
  let d : ℝ := (R+1 : ℕ)
  let L := halfUpperTruncation EA
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hd : 0 ≤ d := le_trans (by norm_num) hd1
  have hL : ‖L‖ ≤ d * η := (halfUpperTruncation_opNorm_le R EA).trans
    (mul_le_mul_of_nonneg_left hEA hd)
  have hLt : ‖L.transpose‖ ≤ d * η := by rw [matrix_transpose_opNorm]; exact hL
  have hEHt : ‖EH.transpose‖ ≤ η := by rw [matrix_transpose_opNorm]; exact hEH
  have hLs := dyadic_sq_le_of_operator_bound R L s (d*η) (mul_nonneg hd hη) hL hs
  have hLts := dyadic_sq_le_of_operator_bound R L.transpose s (d*η)
    (mul_nonneg hd hη) hLt hs
  have hLb := dyadic_sq_le_of_operator_bound R L b (d*η) (mul_nonneg hd hη) hL hb
  have hHs := dyadic_sq_le_of_operator_bound R EH s η hη hEH hs
  have hHts := dyadic_sq_le_of_operator_bound R EH.transpose s η hη hEHt hs
  have heq2 := (sq_le_sq₀ (norm_nonneg eq) hη).2 heq
  have hev2 := (sq_le_sq₀ (norm_nonneg ev) hη).2 hev
  let Q := ‖eq‖^2 + ‖ev‖^2 + dyadicMatrixSeminorm R s L^2 +
    dyadicMatrixSeminorm R s L.transpose^2 + dyadicMatrixSeminorm R b L^2 +
    dyadicMatrixSeminorm R s EH^2 + dyadicMatrixSeminorm R s EH.transpose^2
  have hQ : Q ≤ 7*d^3*η^2 := by
    have hdd3 : d ≤ d^3 := by
      nlinarith [mul_nonneg hd (show 0 ≤ d^2-1 by nlinarith)]
    have hd31 : 1 ≤ d^3 := by
      nlinarith [mul_nonneg (show 0 ≤ d-1 by linarith)
        (show 0 ≤ d^2+d+1 by positivity)]
    have hm1 := mul_le_mul_of_nonneg_right hdd3 (sq_nonneg η)
    have hm2 := mul_le_mul_of_nonneg_right hd31 (sq_nonneg η)
    dsimp only [Q]
    change _ ≤ d*(d*η)^2 at hLs hLts hLb
    change _ ≤ d*η^2 at hHs hHts
    nlinarith
  have hlin1 : |inner (𝕜 := ℝ) eq b| ≤ η := by
    calc
      _ ≤ ‖eq‖ * ‖b‖ := abs_real_inner_le_norm _ _
      _ ≤ η * 1 := mul_le_mul heq hb (norm_nonneg _) hη
      _ = η := mul_one _
  have hlin2 : |inner (𝕜 := ℝ) s
      (Matrix.toEuclideanCLM (n := Fin (2^R)) (𝕜 := ℝ) L b)| ≤ d*η := by
    calc
      _ ≤ ‖s‖ * ‖L‖ * ‖b‖ := inner_matrix_abs_le _ _ _
      _ ≤ 1 * (d*η) * 1 := by gcongr
      _ = _ := by ring
  have hlin3 : |inner (𝕜 := ℝ) s ev| ≤ η := by
    calc
      _ ≤ ‖s‖ * ‖ev‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * η := mul_le_mul hs hev (norm_nonneg _) (by norm_num)
      _ = η := one_mul _
  have hlin4 : |inner (𝕜 := ℝ) s
      (Matrix.toEuclideanCLM (n := Fin (2^R)) (𝕜 := ℝ) (fullUpperTruncation EH) s)| ≤ d*η := by
    have hT : ‖fullUpperTruncation EH‖ ≤ d*η :=
      (fullUpperTruncation_opNorm_le R EH).trans (mul_le_mul_of_nonneg_left hEH hd)
    calc
      _ ≤ ‖s‖ * ‖fullUpperTruncation EH‖ * ‖s‖ := inner_matrix_abs_le _ _ _
      _ ≤ 1 * (d*η) * 1 := by gcongr
      _ = _ := by ring
  let lin := inner (𝕜 := ℝ) eq b - inner (𝕜 := ℝ) s
    (Matrix.toEuclideanCLM (n := Fin (2^R)) (𝕜 := ℝ) L b) +
    inner (𝕜 := ℝ) s ev - inner (𝕜 := ℝ) s
    (Matrix.toEuclideanCLM (n := Fin (2^R)) (𝕜 := ℝ) (fullUpperTruncation EH) s)
  have hlin : |lin| ≤ (2*d+2)*η := by
    calc
      _ ≤ (|inner (𝕜 := ℝ) eq b| + |inner (𝕜 := ℝ) s
          (Matrix.toEuclideanCLM (n := Fin (2^R)) (𝕜 := ℝ) L b)|) +
          |inner (𝕜 := ℝ) s ev| + |inner (𝕜 := ℝ) s
          (Matrix.toEuclideanCLM (n := Fin (2^R)) (𝕜 := ℝ) (fullUpperTruncation EH) s)| :=
        (abs_sub _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ ≤ _ := by linarith
  obtain ⟨C, hu, hdg, hg, hi, _, _, hf⟩ :=
    exists_upper_cholesky_with_quadratic_energy_bound R η EA H0 EH s eq b ev
      hη hsmall hEA hsym hH0 hEH
  refine ⟨C, hu, hdg, hg, hi, ?_⟩
  change |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) -
    inner (𝕜 := ℝ) s b - lin| ≤ 200*d*Q at hf
  calc
    _ = |(queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) -
        inner (𝕜 := ℝ) s b - lin) + lin| := by congr 1; ring
    _ ≤ |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) -
        inner (𝕜 := ℝ) s b - lin| + |lin| := abs_add_le _ _
    _ ≤ 200*d*Q + (2*d+2)*η := add_le_add hf hlin
    _ ≤ 200*d*(7*d^3*η^2) + (2*d+2)*η :=
      add_le_add (mul_le_mul_of_nonneg_left hQ (show 0 ≤ 200*d by positivity)) le_rfl
    _ = queryError R η := by dsimp [queryError, d]; push_cast; ring

theorem upper_cholesky_unique {k : ℕ} (C D : Matrix (Fin k) (Fin k) ℝ)
    (hC : ∀ i j, j < i → C i j = 0) (hD : ∀ i j, j < i → D i j = 0)
    (hCp : ∀ i, 0 < C i i) (hDp : ∀ i, 0 < D i i)
    (hgram : C.transpose*C = D.transpose*D) : C = D := by
  have hall : ∀ v : ℕ, ∀ i : Fin k, i.val = v → ∀ j, C i j = D i j := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro i hi
      have hprod (j : Fin k) : C i i*C i j = D i i*D i j := by
        have he := congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A i j) hgram
        simp only [Matrix.mul_apply, Matrix.transpose_apply] at he
        have hsum : (∑ l : Fin k, (C l i*C l j - D l i*D l j)) =
            C i i*C i j - D i i*D i j := by
          apply Finset.sum_eq_single i
          · intro l _ hli
            rcases lt_or_gt_of_ne hli with hl | hl
            · have hli' : l.val < v := by
                change l.val < i.val at hl
                omega
              rw [ih l.val hli' l rfl i, ih l.val hli' l rfl j, sub_self]
            · rw [hC l i hl, hD l i hl]
              ring
          · simp
        rw [Finset.sum_sub_distrib, he, sub_self] at hsum
        linarith
      have hii : C i i = D i i := by nlinarith [hprod i, hCp i, hDp i]
      intro j
      have hj := hprod j
      rw [hii] at hj
      exact mul_left_cancel₀ (ne_of_gt (hDp i)) hj
  ext i j
  exact hall i.val i rfl j

theorem upper_cholesky_energy_of_operator_errors
    (R : ℕ) (η : ℝ)
    (EA C H0 EH : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2^R)))
    (hη : 0 ≤ η) (hsmall : 16 * ((R+1 : ℕ) : ℝ)^2 * η ≤ 1)
    (hEA : ‖EA‖ ≤ η) (hsym : EA.transpose = EA)
    (hCu : ∀ i j, j < i → C i j = 0) (hCp : ∀ i, 0 < C i i)
    (hCg : C.transpose*C = 1+EA)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0)
    (hEH : ‖EH‖ ≤ η) (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η)
    (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    |queryEnergyNormalForm C (H0+EH) (s+eq) (b+ev) - inner (𝕜 := ℝ) s b| ≤
      queryError R η := by
  obtain ⟨D, hDu, hDp, hDg, _, hbound⟩ :=
    exists_upper_cholesky_energy_of_operator_errors R η EA H0 EH s eq b ev
      hη hsmall hEA hsym hH0 hEH heq hev hs hb
  have hCD := upper_cholesky_unique C D hCu hDu hCp hDp (hCg.trans hDg.symm)
  simpa only [hCD] using hbound

end SKConstants.Completion.LC5
