module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity

theorem actual_high_one_error_price_le
    {C₀ C W Z F₁ F₂ : ℝ} (hC : 0 ≤ C) (hC₀ : C₀ ≤ C)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z) (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) :
    C₀*W^2*Z*F₁ ≤ C*W*Z*(F₂+W*F₁) := by
  have H:=mul_le_mul_of_nonneg_right hC₀
    (mul_nonneg (mul_nonneg (sq_nonneg W) hZ) hF₁)
  calc
    _ ≤ C*W^2*Z*F₁:=by convert H using 1 <;> ring
    _ = C*W*Z*(W*F₁):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hF₂)
      (mul_nonneg (mul_nonneg hC hW) hZ)

theorem actual_high_two_error_price_le
    {C₁ C W Z F₁ F₂ : ℝ} (hC : 0 ≤ C) (hC₁ : C₁ ≤ C)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z) (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) :
    C₁*W*Z*F₂ ≤ C*W*Z*(F₂+W*F₁) := by
  have H:=mul_le_mul_of_nonneg_right hC₁
    (mul_nonneg (mul_nonneg hW hZ) hF₂)
  calc
    _ ≤ C*W*Z*F₂:=by convert H using 1 <;> ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hW hF₁))
      (mul_nonneg (mul_nonneg hC hW) hZ)

theorem actual_high_transient_price_le
    {C₂ C W Z F₁ F₂ : ℝ} (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂) (hC₂C : C₂ ≤ C)
    (hW : 0 ≤ W) (hW₁ : W ≤ 1) (hZ : 0 ≤ Z) (hF₁ : 0 ≤ F₁) (hF₂ : 0 ≤ F₂) :
    C₂*W^3*Z*F₁ ≤ C*W*Z*(F₂+W*F₁) := by
  have HW : W^3 ≤ W^2:=by
    have H:=mul_le_mul_of_nonneg_right hW₁ (sq_nonneg W)
    nlinarith only [H]
  have H:=mul_le_mul_of_nonneg_left HW (mul_nonneg (mul_nonneg hC₂ hZ) hF₁)
  apply (show C₂*W^3*Z*F₁ ≤ C₂*W^2*Z*F₁ by convert H using 1 <;> ring).trans
  exact actual_high_one_error_price_le hC hC₂C hW hZ hF₁ hF₂

end OAI.SKFluctuations.Cavity
