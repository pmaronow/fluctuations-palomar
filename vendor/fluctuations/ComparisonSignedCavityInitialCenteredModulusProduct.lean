module

public import ComparisonSignedCavityCenteredTransientLowPartsBound

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set
set_option maxHeartbeats 20000000

theorem native_centered_initial_LOW_modulus_product_bound
    {W Z xs d l : ℝ} (hW : 0<W) (hW1 : W≤1) (hZ : 0≤Z) (hxs : 0≤xs) (hd : 0≤d)
    (hl : l∈Icc (0:ℝ) 1) (A B f g : Fin 4→ℝ) (J2 J3 : ℝ)
    (hA : ∀i,0≤A i) (hB : ∀i,0≤B i)
    (hJ2 : |J2|≤A 2*W*Z*xs*d) (hJ3 : |J3|≤A 3*W^2*Z*xs*d)
    (hf : ∀i,|f i|≤A i*W^((i:ℕ)-1)*Z*xs*d) (hg : ∀i,|g i|≤B i*W^(i:ℕ)) :
    |l*(J3-productJet3 g f 3)+3*(J2-productJet3 g f 2)|≤
      ((A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0)+
        3*(A 2+B 0*A 2+2*B 1*A 1+B 2*A 0))*W*Z*xs*d := by
  let Cost:=xs*d/W
  have hCost : 0≤Cost:=div_nonneg (mul_nonneg hxs hd) hW.le
  have Hxs : xs*d≤Cost:=by
    apply (le_div_iff₀ hW).mpr
    exact mul_le_of_le_one_right (mul_nonneg hxs hd) hW1
  have Hf i : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    apply (hf i).trans
    fin_cases i
    · norm_num
      have H:=mul_le_mul_of_nonneg_left Hxs (mul_nonneg (hA 0) hZ)
      convert H using 1
      ring
    · norm_num
      apply le_of_eq
      dsimp [Cost]
      field_simp
    · norm_num
      apply le_of_eq
      dsimp [Cost]
      field_simp
    · norm_num
      apply le_of_eq
      dsimp [Cost]
      field_simp
  have H2 : |J2|≤A 2*W^2*Z*Cost:=by
    apply hJ2.trans_eq
    dsimp [Cost]
    field_simp
  have H3 : |J3|≤A 3*W^3*Z*Cost:=by
    apply hJ3.trans_eq
    dsimp [Cost]
    field_simp
  have H:=native_centered_LOW_parts_product_bound hW.le hW1 hZ hCost hl A B f g J2 J3 hA hB H2 H3 Hf hg
  apply H.trans_eq
  dsimp [Cost]
  field_simp

end OAI.SKFluctuations.Cavity
