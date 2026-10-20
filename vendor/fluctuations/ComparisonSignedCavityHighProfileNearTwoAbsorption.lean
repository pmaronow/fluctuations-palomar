module

public import ComparisonSignedCavityOriginalHighProfileYoung

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity

theorem native_high_profile_near_two_absorption {N x W eta theta : ℝ}
    (hN : 1 ≤ N) (hx : 0 < x) (hxW : x ≤ W) (hxN : 1/N ≤ x)
    (heta : 0 < eta) (htheta1 : 1 ≤ theta) (htheta2 : theta ≤ 2)
    (hdeficit : 2-theta ≤ eta/128) :
    (N^(-eta/32)*x^2/W)^theta ≤ N^(-eta/128)*x^2 := by
  have hN0 : 0 < N:=zero_lt_one.trans_le hN
  have hW : 0 < W:=hx.trans_le hxW
  have htheta : 0 ≤ theta:=zero_le_one.trans htheta1
  have HB : N^(-eta/32)*x^2/W ≤ N^(-eta/32)*x := by
    have HX : x^2/W ≤ x := (div_le_iff₀ hW).mpr (by nlinarith)
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left HX (Real.rpow_nonneg hN0.le _)
  have Hpow:=Real.rpow_le_rpow (by positivity : 0 ≤ N^(-eta/32)*x^2/W) HB htheta
  have Hinv : x^(theta-2) ≤ N^(2-theta) := by
    have H:=Real.rpow_le_rpow_of_nonpos (one_div_pos.mpr hN0) hxN (sub_nonpos.mpr htheta2)
    rw [one_div,←Real.rpow_neg_one,←Real.rpow_mul hN0.le] at H
    have HE : (-1:ℝ)*(theta-2)=2-theta:=by ring
    simpa only [HE] using H
  have HX : x^theta ≤ N^(2-theta)*x^2 := by
    calc
      _=x^(theta-2)*x^2 := by
        rw [←Real.rpow_two,←Real.rpow_add hx]
        congr 1
        ring
      _≤_:=mul_le_mul_of_nonneg_right Hinv (sq_nonneg x)
  have Hexp : (-eta/32)*theta+(2-theta) ≤ -eta/128 := by
    nlinarith [mul_le_mul_of_nonneg_left htheta1 heta.le]
  calc
    _≤(N^(-eta/32)*x)^theta := Hpow
    _=N^((-eta/32)*theta)*x^theta := by
      rw [Real.mul_rpow (Real.rpow_nonneg hN0.le _) hx.le,←Real.rpow_mul hN0.le]
    _≤N^((-eta/32)*theta)*(N^(2-theta)*x^2) :=
      mul_le_mul_of_nonneg_left HX (Real.rpow_nonneg hN0.le _)
    _=N^((-eta/32)*theta+(2-theta))*x^2 := by
      rw [←mul_assoc,←Real.rpow_add hN0]
    _≤_:=mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN Hexp) (sq_nonneg x)

theorem native_high_profile_low_factor_identity {N x W eta : ℝ} (hW : W≠0) :
    W*(N^(-eta/32)*x^2/W)=N^(-eta/32)*x^2 := by
  field_simp

theorem exists_native_high_profile_holder_orders {eta : ℝ} (heta : 0 < eta) :
    ∃(p : ℝ) (dOrder : ℕ),2 < p ∧ 0 < dOrder ∧ p/(p-2) ≤ (dOrder:ℝ) ∧
      1 ≤ 4/p ∧ 4/p < 2 ∧ 2-4/p ≤ eta/128 := by
  let gap:=min (eta/256) (1/2:ℝ)
  let theta:=2-gap
  let p:=4/theta
  have hgap : 0 < gap:=lt_min (by positivity) (by norm_num)
  have hgapHalf : gap ≤ (1/2:ℝ):=min_le_right _ _
  have hgapEta : gap ≤ eta/256:=min_le_left _ _
  have htheta0 : 0 < theta:=by dsimp only [theta];linarith
  have htheta1 : 1 ≤ theta:=by dsimp only [theta];linarith
  have htheta2 : theta < 2:=by dsimp only [theta];linarith
  have hp : 2 < p:=by
    dsimp only [p]
    apply (lt_div_iff₀ htheta0).mpr
    linarith
  have htheta : 4/p=theta := by
    dsimp only [p]
    field_simp
  have hratio : 0 < p/(p-2):=div_pos (by linarith) (by linarith)
  obtain ⟨dOrder,hdOrder⟩:=exists_nat_gt (p/(p-2))
  have hdReal : 0 < (dOrder:ℝ):=hratio.trans hdOrder
  have hdNat : 0 < dOrder:=by exact_mod_cast hdReal
  refine ⟨p,dOrder,hp,hdNat,hdOrder.le,?_,?_,?_⟩
  · rw [htheta]
    exact htheta1
  · rw [htheta]
    exact htheta2
  · rw [htheta]
    dsimp only [theta]
    linarith

end OAI.SKFluctuations.Cavity
