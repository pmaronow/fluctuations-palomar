module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set
open scoped NNReal

theorem positiveReciprocal_lipschitzOn {B : ℝ} (hB : 0<B) :
    LipschitzOnWith ⟨(B^2)⁻¹,inv_nonneg.mpr (sq_nonneg B)⟩ (fun x : ℝ=>x⁻¹) (Ici B) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxp : 0<x := hB.trans_le hx
  have hyp : 0<y := hB.trans_le hy
  have hBB : B^2≤x*y := by nlinarith [mul_le_mul hx hy hB.le hxp.le]
  have hi : (x*y)⁻¹≤(B^2)⁻¹ := (inv_le_inv₀ (mul_pos hxp hyp) (sq_pos_of_pos hB)).mpr hBB
  change |x⁻¹-y⁻¹|≤(B^2)⁻¹*|x-y|
  rw [inv_sub_inv hxp.ne' hyp.ne',abs_div,abs_of_pos (mul_pos hxp hyp),abs_sub_comm,div_eq_mul_inv]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (abs_nonneg (x-y))

end OAI.SKFluctuations.LaplaceWindowFormalization
