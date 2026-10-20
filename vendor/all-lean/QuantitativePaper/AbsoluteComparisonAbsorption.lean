module

public import QuantitativePaper.AbsoluteComparisonAbsorptionPowers

@[expose] public section

/-! Uniform final absorption from the genuine prior comparison and the
absolute interpolation budget. -/
noncomputable section
namespace QuantitativePaper
set_option maxHeartbeats 500000

def absoluteComparisonAbsorptionConstant (C C0 C1 : ℝ) : ℝ :=
  C*(1+C0^((1:ℝ)/11)+C1^((1:ℝ)/11))+1

theorem absoluteComparisonAbsorptionConstant_pos (C C0 C1 : ℝ)
    (hC : 0≤C) (hC0 : 0≤C0) (hC1 : 0≤C1) :
    0<absoluteComparisonAbsorptionConstant C C0 C1 := by
  have ha:=Real.rpow_nonneg hC0 ((1:ℝ)/11)
  have hb:=Real.rpow_nonneg hC1 ((1:ℝ)/11)
  have hc:=mul_nonneg hC (show 0≤1+C0^((1:ℝ)/11)+C1^((1:ℝ)/11) by positivity)
  unfold absoluteComparisonAbsorptionConstant
  linarith

theorem absoluteComparison_budget_power (N l e C0 C1 : ℝ)
    (hN : 0<N) (hl : 0<l) (hl1 : l≤1) (he : 0≤e)
    (hC0 : 0≤C0) (hC1 : 0≤C1)
    (hprior : e≤C0*(N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3))) :
    (N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3))*(e+C1*l^5)^((1:ℝ)/11)≤
      C0^((1:ℝ)/11)*(N^(-(2:ℝ)/3)+N^(-(3:ℝ)/4)*l^(-(1:ℝ)/2))+
        C1^((1:ℝ)/11)*N^(-(2:ℝ)/3) := by
  let X:=N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3)
  have hX : 0<X:=mul_pos (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hl _)
  have hl5 : 0≤l^5:=pow_nonneg hl.le _
  have hp : (e+C1*l^5)^((1:ℝ)/11)≤
      (C0*X)^((1:ℝ)/11)+(C1*l^5)^((1:ℝ)/11):=
    (Real.rpow_le_rpow (add_nonneg he (mul_nonneg hC1 hl5))
      (by simpa only [add_comm] using add_le_add_right hprior (C1*l^5)) (by norm_num)).trans
      (Real.rpow_add_le_add_rpow (mul_nonneg hC0 hX.le) (mul_nonneg hC1 hl5)
        (by norm_num) (by norm_num))
  have hxp : X*X^((1:ℝ)/11)=X^((12:ℝ)/11):=by
    calc
      _=X^(1:ℝ)*X^((1:ℝ)/11):=by rw [Real.rpow_one]
      _=X^(1+(1:ℝ)/11):=(Real.rpow_add hX _ _).symm
      _=_:=by norm_num
  calc
    _≤X*((C0*X)^((1:ℝ)/11)+(C1*l^5)^((1:ℝ)/11)):=
      mul_le_mul_of_nonneg_left hp hX.le
    _=C0^((1:ℝ)/11)*X^((12:ℝ)/11)+C1^((1:ℝ)/11)*(X*(l^5)^((1:ℝ)/11)):=by
      rw [Real.mul_rpow hC0 hX.le,Real.mul_rpow hC1 hl5]
      simp only [mul_add]
      rw [show X*(C0^((1:ℝ)/11)*X^((1:ℝ)/11))=
        C0^((1:ℝ)/11)*(X*X^((1:ℝ)/11)) by ring,hxp]
      ring
    _≤_:=add_le_add
      (mul_le_mul_of_nonneg_left (absoluteComparison_power_le N l hN hl)
        (Real.rpow_nonneg hC0 _))
      (mul_le_mul_of_nonneg_left (absoluteComparison_trial_power_le N l hN hl hl1)
        (Real.rpow_nonneg hC1 _))

theorem absoluteComparison_absorb (N l e C C0 C1 : ℝ)
    (hN : 0<N) (hl : 0<l) (hl1 : l≤1) (he : 0≤e)
    (hC : 0≤C) (hC0 : 0≤C0) (hC1 : 0≤C1)
    (hprior : e≤C0*(N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3)))
    (hbudget : e≤C*(N^(-(2:ℝ)/3)+N^(-(3:ℝ)/4)*l^(-(1:ℝ)/2)+
      Real.log (2+N)/(N*l)+(N^(-(2:ℝ)/3)*l^(-(1:ℝ)/3))*(e+C1*l^5)^((1:ℝ)/11))) :
    e≤absoluteComparisonAbsorptionConstant C C0 C1*
      (N^(-(2:ℝ)/3)+N^(-(3:ℝ)/4)*l^(-(1:ℝ)/2)+Real.log (2+N)/(N*l)) := by
  have ha:=Real.rpow_nonneg hN.le (-(2:ℝ)/3)
  have hb:=mul_nonneg (Real.rpow_nonneg hN.le (-(3:ℝ)/4))
    (Real.rpow_nonneg hl.le (-(1:ℝ)/2))
  have hd : 0≤Real.log (2+N)/(N*l):=
    div_nonneg (Real.log_nonneg (by linarith)) (mul_nonneg hN.le hl.le)
  have hp:=absoluteComparison_budget_power N l e C0 C1 hN hl hl1 he hC0 hC1 hprior
  have h0:=Real.rpow_nonneg hC0 ((1:ℝ)/11)
  have h1:=Real.rpow_nonneg hC1 ((1:ℝ)/11)
  have hs : 0≤N^(-(2:ℝ)/3)+N^(-(3:ℝ)/4)*l^(-(1:ℝ)/2)+Real.log (2+N)/(N*l):=by positivity
  unfold absoluteComparisonAbsorptionConstant
  calc
    e≤C*((1+C0^((1:ℝ)/11)+C1^((1:ℝ)/11))*
      (N^(-(2:ℝ)/3)+N^(-(3:ℝ)/4)*l^(-(1:ℝ)/2)+Real.log (2+N)/(N*l))):=
      hbudget.trans (mul_le_mul_of_nonneg_left (by nlinarith) hC)
    _≤_:=by nlinarith

end QuantitativePaper
