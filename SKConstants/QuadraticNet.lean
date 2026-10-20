module

public import SKConstants.SKDisorderNorm
public import Mathlib.Analysis.InnerProductSpace.Symmetric

public section
noncomputable section
open scoped InnerProductSpace

namespace SKConstants

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma quadratic_abs_bound_from_unit (A : E →L[ℝ] E) (b : ℝ)
    (hquad : ∀ x : E, ‖x‖ = 1 → |⟪A x, x⟫_ℝ| ≤ b) (x : E) :
    |⟪A x, x⟫_ℝ| ≤ b * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : E := ‖x‖⁻¹ • x
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, inv_mul_cancel₀ hp.ne']
  have hxy : ‖x‖ • y = x := by
    simp [y, smul_smul, mul_inv_cancel₀ hp.ne']
  have hh := mul_le_mul_of_nonneg_left (hquad y hy) (sq_nonneg ‖x‖)
  have he : |⟪A x, x⟫_ℝ| = ‖x‖ ^ 2 * |⟪A y, y⟫_ℝ| := by
    conv_lhs => rw [← hxy]
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [abs_mul, abs_of_nonneg (norm_nonneg x)]
    ring
  rw [he]
  nlinarith

lemma symmetric_opNorm_le_of_unit_quadratic (A : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ)
    (b : ℝ) (hb : 0 ≤ b)
    (hquad : ∀ x : E, ‖x‖ = 1 → |⟪A x, x⟫_ℝ| ≤ b) :
    ‖A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hb
  intro x y hx hy
  have hp := quadratic_abs_bound_from_unit A b hquad (x + y)
  have hm := quadratic_abs_bound_from_unit A b hquad (x - y)
  have he : ⟪A (x + y), x + y⟫_ℝ - ⟪A (x - y), x - y⟫_ℝ =
      4 * ⟪A x, y⟫_ℝ := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right]
    rw [hsym y x, real_inner_comm y (A x)]
    ring
  have hh := (abs_sub_le ⟪A (x + y), x + y⟫_ℝ
    0 ⟪A (x - y), x - y⟫_ℝ)
  simp only [sub_zero, zero_sub, abs_neg] at hh
  have hh := hh.trans (add_le_add hp hm)
  rw [he, abs_mul] at hh
  norm_num at hh
  have hpara := parallelogram_law_with_norm ℝ x y
  rw [hx, hy] at hpara
  simp only [RCLike.re_to_real]
  nlinarith [le_abs_self ⟪A x, y⟫_ℝ]

theorem symmetric_opNorm_le_of_quarter_net (A : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪A x, y⟫_ℝ = ⟪x, A y⟫_ℝ)
    (N : Finset E) (hN : ∀ x ∈ N, ‖x‖ ≤ 1)
    (hcover : ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ N, dist x y ≤ (1 / 4 : ℝ))
    (b : ℝ) (hb : 0 ≤ b)
    (hquad : ∀ x ∈ N, |⟪A x, x⟫_ℝ| ≤ b) : ‖A‖ ≤ 2 * b := by
  have hnorm : ‖A‖ ≤ b + ‖A‖ / 2 := by
    apply symmetric_opNorm_le_of_unit_quadratic A hsym _ (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx.le
    have h1 : |⟪A (x - y), x⟫_ℝ| ≤ ‖A‖ / 4 := by
      calc
        _ ≤ ‖A (x - y)‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = ‖A (x - y)‖ := by rw [hx, mul_one]
        _ ≤ ‖A‖ * ‖x - y‖ := A.le_opNorm _
        _ ≤ ‖A‖ * (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left
          (by simpa only [dist_eq_norm] using hxy) (norm_nonneg _)
        _ = _ := by ring
    have h2 : |⟪A y, x - y⟫_ℝ| ≤ ‖A‖ / 4 := by
      calc
        _ ≤ ‖A y‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖y‖) * (1 / 4 : ℝ) := by
          gcongr
          · exact A.le_opNorm _
          · simpa only [dist_eq_norm] using hxy
        _ ≤ (‖A‖ * 1) * (1 / 4 : ℝ) := by gcongr; exact hN y hy
        _ = _ := by ring
    have he : ⟪A x, x⟫_ℝ = ⟪A (x - y), x⟫_ℝ +
        ⟪A y, x - y⟫_ℝ + ⟪A y, y⟫_ℝ := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans
      (add_le_add h1 h2)) (hquad y hy)).trans_eq (by ring))
  linarith

end SKConstants
