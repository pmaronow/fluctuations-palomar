module

public import ComparisonSignedCavityCenteredTransientHighThird

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set
set_option maxHeartbeats 16000000

theorem native_centered_LOW_third_coefficient_nonneg {A B : Fin 4→ℝ}
    (hA : ∀i,0≤A i) (hB : ∀i,0≤B i) :
    0≤A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0 := by
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (hA 3)
    (mul_nonneg (hB 0) (hA 3))) (mul_nonneg (mul_nonneg (by norm_num) (hB 1)) (hA 2)))
    (mul_nonneg (mul_nonneg (by norm_num) (hB 2)) (hA 1))) (mul_nonneg (hB 3) (hA 0))

theorem native_centered_LOW_second_coefficient_nonneg {A B : Fin 4→ℝ}
    (hA : ∀i,0≤A i) (hB : ∀i,0≤B i) :
    0≤A 2+B 0*A 2+2*B 1*A 1+B 2*A 0 := by
  exact add_nonneg (add_nonneg (add_nonneg (hA 2) (mul_nonneg (hB 0) (hA 2)))
    (mul_nonneg (mul_nonneg (by norm_num) (hB 1)) (hA 1))) (mul_nonneg (hB 2) (hA 0))

theorem native_centered_LOW_second_product_bound
    {W Z Cost J : ℝ} (hW : 0≤W) (A B f g : Fin 4→ℝ) (hB : ∀i,0≤B i)
    (hJ : |J|≤A 2*W^2*Z*Cost)
    (hf : ∀i,|f i|≤A i*W^(i:ℕ)*Z*Cost)
    (hg : ∀i,|g i|≤B i*W^(i:ℕ)) :
    |J-productJet3 g f 2|≤(A 2+B 0*A 2+2*B 1*A 1+B 2*A 0)*W^2*Z*Cost := by
  have Hterm (i j : Fin 4) : |g i*f j|≤(B i*W^(i:ℕ))*(A j*W^(j:ℕ)*Z*Cost):=by
    rw [abs_mul]
    exact mul_le_mul (hg i) (hf j) (abs_nonneg _) (mul_nonneg (hB i) (pow_nonneg hW _))
  have H02:=Hterm 0 2
  have H11:=Hterm 1 1
  have H20:=Hterm 2 0
  norm_num at H02 H11 H20
  simp only [←abs_mul] at H02 H11 H20
  have H11' : |2*g 1*f 1|≤2*((B 1*W)*(A 1*W*Z*Cost)):=by
    calc
      _=2*|g 1*f 1|:=by rw [mul_assoc,abs_mul];norm_num
      _≤_:=mul_le_mul_of_nonneg_left H11 (by norm_num)
  have Hp : |productJet3 g f 2|≤(B 0*A 2+2*B 1*A 1+B 2*A 0)*W^2*Z*Cost:=by
    have HH:=((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add H02 H11')) H20))
    change |g 0*f 2+2*g 1*f 1+g 2*f 0|≤_
    nlinarith only [HH]
  exact (abs_sub _ _).trans (by nlinarith only [hJ,Hp])

theorem native_centered_LOW_parts_product_bound
    {W Z Cost l : ℝ} (hW : 0≤W) (hW1 : W≤1) (hZ : 0≤Z) (hCost : 0≤Cost)
    (hl : l∈Icc (0:ℝ) 1) (A B f g : Fin 4→ℝ) (J2 J3 : ℝ)
    (hA : ∀i,0≤A i) (hB : ∀i,0≤B i)
    (hJ2 : |J2|≤A 2*W^2*Z*Cost) (hJ3 : |J3|≤A 3*W^3*Z*Cost)
    (hf : ∀i,|f i|≤A i*W^(i:ℕ)*Z*Cost) (hg : ∀i,|g i|≤B i*W^(i:ℕ)) :
    |l*(J3-productJet3 g f 3)+3*(J2-productJet3 g f 2)|≤
      ((A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0)+
        3*(A 2+B 0*A 2+2*B 1*A 1+B 2*A 0))*W^2*Z*Cost := by
  let c3:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0
  let c2:=A 2+B 0*A 2+2*B 1*A 1+B 2*A 0
  have hc3 : 0≤c3:=native_centered_LOW_third_coefficient_nonneg hA hB
  have hc2 : 0≤c2:=native_centered_LOW_second_coefficient_nonneg hA hB
  have H3:=native_centered_third_HIGH_product_bound hW hZ hCost A B f g hA hB hJ3 hf hg
  have H2:=native_centered_LOW_second_product_bound hW A B f g hB hJ2 hf hg
  have Hpow : W^3≤W^2:=by nlinarith only [sq_nonneg W,mul_le_mul_of_nonneg_left hW1 (sq_nonneg W)]
  have H3small : |J3-productJet3 g f 3|≤c3*W^2*Z*Cost:=
    H3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hpow hc3) hZ) hCost)
  have Hl : |l*(J3-productJet3 g f 3)|≤c3*W^2*Z*Cost:=by
    rw [abs_mul,abs_of_nonneg hl.1]
    exact (mul_le_mul_of_nonneg_left H3small hl.1).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hl.2
        (mul_nonneg (mul_nonneg (mul_nonneg hc3 (sq_nonneg W)) hZ) hCost)))
  have H2scale : |3*(J2-productJet3 g f 2)|≤3*(c2*W^2*Z*Cost):=by
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤3)]
    exact mul_le_mul_of_nonneg_left H2 (by norm_num)
  exact (abs_add_le _ _).trans (by nlinarith only [Hl,H2scale])

end OAI.SKFluctuations.Cavity
