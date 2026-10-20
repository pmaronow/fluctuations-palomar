module

public import SKConstants.Completion.LGram.Compression
import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
namespace SKConstants.Completion.LGram
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open LC5

def sevenErrorSum (R : ℕ) (EA EH : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2^R))) : ℝ :=
  ‖eq‖^2 + ‖ev‖^2 + dyadicMatrixSeminorm R s (halfUpperTruncation EA)^2 +
    dyadicMatrixSeminorm R s (halfUpperTruncation EA).transpose^2 +
    dyadicMatrixSeminorm R b (halfUpperTruncation EA)^2 +
    dyadicMatrixSeminorm R s EH^2 + dyadicMatrixSeminorm R s EH.transpose^2

theorem sevenErrorSum_le_of_operator_errors (R : ℕ) (η : ℝ)
    (EA EH : Matrix (Fin (2^R)) (Fin (2^R)) ℝ)
    (s eq b ev : EuclideanSpace ℝ (Fin (2^R)))
    (hη : 0 ≤ η) (hEA : ‖EA‖ ≤ η) (hEH : ‖EH‖ ≤ η)
    (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η) (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    sevenErrorSum R EA EH s eq b ev ≤ 7 * ((R+1:ℕ):ℝ)^3 * η^2 := by
  let d : ℝ := (R+1:ℕ)
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le R)
  have hd : 0 ≤ d := by linarith
  have hL : ‖halfUpperTruncation EA‖ ≤ d*η :=
    (halfUpperTruncation_opNorm_le R EA).trans (mul_le_mul_of_nonneg_left hEA hd)
  have hLt : ‖(halfUpperTruncation EA).transpose‖ ≤ d*η := by
    rw [matrix_transpose_opNorm]; exact hL
  have hEHt : ‖EH.transpose‖ ≤ η := by rw [matrix_transpose_opNorm]; exact hEH
  have h1 := dyadic_sq_le_of_operator_bound R _ s (d*η) (mul_nonneg hd hη) hL hs
  have h2 := dyadic_sq_le_of_operator_bound R _ s (d*η) (mul_nonneg hd hη) hLt hs
  have h3 := dyadic_sq_le_of_operator_bound R _ b (d*η) (mul_nonneg hd hη) hL hb
  have h4 := dyadic_sq_le_of_operator_bound R _ s η hη hEH hs
  have h5 := dyadic_sq_le_of_operator_bound R _ s η hη hEHt hs
  have h6 := (sq_le_sq₀ (norm_nonneg eq) hη).2 heq
  have h7 := (sq_le_sq₀ (norm_nonneg ev) hη).2 hev
  have hdd : d ≤ d^3 := by nlinarith [mul_nonneg hd (show 0 ≤ d^2-1 by nlinarith)]
  have hd3 : 1 ≤ d^3 := by linarith
  have hm := mul_le_mul_of_nonneg_right hdd (sq_nonneg η)
  have hn := mul_le_mul_of_nonneg_right hd3 (sq_nonneg η)
  change _ ≤ d*(d*η)^2 at h1 h2 h3
  change _ ≤ d*η^2 at h4 h5
  dsimp only [sevenErrorSum]
  change _ ≤ 7*d^3*η^2
  nlinarith

def sevenErrorSumDim (R n : ℕ) (hdim : n=2^R)
    (EA EH : Matrix (Fin n) (Fin n) ℝ) (s eq b ev : EuclideanSpace ℝ (Fin n)) : ℝ := by
  subst n
  exact sevenErrorSum R EA EH s eq b ev

theorem sevenErrorSumDim_le_of_operator_errors (R n : ℕ) (hdim : n=2^R) (η : ℝ)
    (EA EH : Matrix (Fin n) (Fin n) ℝ) (s eq b ev : EuclideanSpace ℝ (Fin n))
    (hη : 0 ≤ η) (hEA : ‖EA‖ ≤ η) (hEH : ‖EH‖ ≤ η)
    (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η) (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    sevenErrorSumDim R n hdim EA EH s eq b ev ≤ 7*((R+1:ℕ):ℝ)^3*η^2 := by
  subst n
  exact sevenErrorSum_le_of_operator_errors R η EA EH s eq b ev hη hEA hEH heq hev hs hb

theorem sevenErrorSum_padded_le_of_operator_errors (R k m : ℕ) (hdim : k+m=2^R) (η : ℝ)
    (EA EH : Matrix (Fin k) (Fin k) ℝ) (s eq b ev : EuclideanSpace ℝ (Fin k))
    (hη : 0 ≤ η) (hEA : ‖EA‖ ≤ η) (hEH : ‖EH‖ ≤ η)
    (heq : ‖eq‖ ≤ η) (hev : ‖ev‖ ≤ η) (hs : ‖s‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    sevenErrorSumDim R (k+m) hdim (padMatrix m EA 0) (padMatrix m EH 0)
      (padVector m s) (padVector m eq) (padVector m b) (padVector m ev) ≤
        7*((R+1:ℕ):ℝ)^3*η^2 :=
  sevenErrorSumDim_le_of_operator_errors R (k+m) hdim η _ _ _ _ _ _ hη
    (by rwa [padMatrix_norm]) (by rwa [padMatrix_norm])
    (by rwa [padVector_norm]) (by rwa [padVector_norm])
    (by rwa [padVector_norm]) (by rwa [padVector_norm])

end SKConstants.Completion.LGram
