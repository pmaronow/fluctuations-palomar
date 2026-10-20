module

public import SKBarriers2.Corner.FrozenRowsPotential3

@[expose] public section

noncomputable section

namespace SKBarriers2.Corner

theorem abs_quadratic_polynomial_le {a b c C g : ℝ} (hC : 0 ≤ C)
    (ha : |a| ≤ C) (hb : |b| ≤ C) (hc : |c| ≤ C) :
    |a + b * g + c * g ^ 2| ≤ 3 * C * (1 + g ^ 2) := by
  have hg : |g| ≤ 1 + g ^ 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  calc
    _ ≤ |a| + |b * g| + |c * g ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C + C * |g| + C * g ^ 2 := by
      rw [abs_mul, abs_mul, abs_pow, sq_abs]
      exact add_le_add (add_le_add ha (mul_le_mul_of_nonneg_right hb (abs_nonneg g)))
        (mul_le_mul_of_nonneg_right hc (sq_nonneg g))
    _ ≤ 3 * C * (1 + g ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hg hC, mul_nonneg hC (sq_nonneg g)]

theorem moving_endpoint_budgets_quadratic {B C K g X Y : ℝ} {n : ℕ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K) (hn : n ≤ 12)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXC : X ≤ C * (1 + |g|)) (hYC : Y ≤ C * (1 + |g|)) :
    let F := (B + 1) * (C + 1) ^ 2
    let L := 4 * F ^ 2 * (1 + 6 * K) ^ 24
    (1 + 6 * K) ^ n * (B * X + 1) ≤ L * (1 + g ^ 2) ∧
      (1 + 6 * K) ^ (2 * n) * (B * (X ^ 2 + Y) + (B * X + 1) ^ 2) ≤
        L * (1 + g ^ 2) := by
  let R := 1 + |g|
  let W := 1 + g ^ 2
  let F := (B + 1) * (C + 1) ^ 2
  let T := (1 + 6 * K) ^ 24
  change X ≤ C * R at hXC
  change Y ≤ C * R at hYC
  have hR : 1 ≤ R := by dsimp only [R]; linarith [abs_nonneg g]
  have hR₀ : 0 ≤ R := by linarith
  have hW : 1 ≤ W := by dsimp only [W]; nlinarith [sq_nonneg g]
  have hF : 1 ≤ F := one_le_mul_of_one_le_of_one_le (by linarith)
    (one_le_pow₀ (by linarith))
  have hF₀ : 0 ≤ F := by linarith
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hR₂ : R ^ 2 ≤ 2 * W := by
    dsimp only [R, W]
    nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  have hRpow : R ≤ R ^ 2 := le_self_pow₀ hR (by norm_num : (2 : ℕ) ≠ 0)
  have hFpow : F ≤ F ^ 2 := le_self_pow₀ hF (by norm_num : (2 : ℕ) ≠ 0)
  have hFC : B * C + 1 ≤ F := by
    dsimp only [F]
    nlinarith [mul_nonneg hB hC, mul_nonneg hB (sq_nonneg C)]
  have hFC₂ : B * (C ^ 2 + C) ≤ F := by
    dsimp only [F]
    nlinarith [mul_nonneg hB hC]
  have hA : B * X + 1 ≤ F * R := by
    calc
      _ ≤ (B * C + 1) * R := by
        have H := mul_le_mul_of_nonneg_left hXC hB
        nlinarith
      _ ≤ F * R := mul_le_mul_of_nonneg_right hFC hR₀
  have hH : B * (X ^ 2 + Y) ≤ F * R ^ 2 := by
    have hX₂ : X ^ 2 ≤ C ^ 2 * R ^ 2 :=
      (pow_le_pow_left₀ hX hXC 2).trans_eq (by ring)
    have hY₂ : Y ≤ C * R ^ 2 :=
      hYC.trans (mul_le_mul_of_nonneg_left hRpow hC)
    calc
      _ ≤ B * ((C ^ 2 + C) * R ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hB
      _ ≤ F * R ^ 2 := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hFC₂ (sq_nonneg R)
  have hA₂ : (B * X + 1) ^ 2 ≤ F ^ 2 * R ^ 2 :=
    (pow_le_pow_left₀ (by positivity) hA 2).trans_eq (by ring)
  have hsum : B * (X ^ 2 + Y) + (B * X + 1) ^ 2 ≤ 4 * F ^ 2 * W := by
    calc
      _ ≤ (F + F ^ 2) * R ^ 2 := (add_le_add hH hA₂).trans_eq (by ring)
      _ ≤ (2 * F ^ 2) * R ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg R)
      _ ≤ (2 * F ^ 2) * (2 * W) := mul_le_mul_of_nonneg_left hR₂ (by positivity)
      _ = _ := by ring
  have hlinear : B * X + 1 ≤ 4 * F ^ 2 * W := by
    have hFR : 1 ≤ F * R := one_le_mul_of_one_le_of_one_le hF hR
    calc
      _ ≤ F * R := hA
      _ ≤ (F * R) ^ 2 := le_self_pow₀ hFR (by norm_num : (2 : ℕ) ≠ 0)
      _ = F ^ 2 * R ^ 2 := mul_pow _ _ _
      _ ≤ F ^ 2 * (2 * W) := mul_le_mul_of_nonneg_left hR₂ (sq_nonneg F)
      _ ≤ 4 * F ^ 2 * W := by nlinarith [mul_nonneg (sq_nonneg F) (by linarith : 0 ≤ W)]
  have hpower₁ : (1 + 6 * K) ^ n ≤ T :=
    pow_le_pow_right₀ (by linarith) (by omega : n ≤ 24)
  have hpower₂ : (1 + 6 * K) ^ (2 * n) ≤ T :=
    pow_le_pow_right₀ (by linarith) (by omega : 2 * n ≤ 24)
  constructor
  · exact (mul_le_mul hpower₁ hlinear (by positivity) hT).trans_eq (by dsimp only [T]; ring)
  · exact (mul_le_mul hpower₂ hsum (by positivity) hT).trans_eq (by dsimp only [T]; ring)

end SKBarriers2.Corner
