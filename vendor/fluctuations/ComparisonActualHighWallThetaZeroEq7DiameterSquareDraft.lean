module

public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_lambda_energy_sixth_draft
    {N d E lam : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hupper : Real.sqrt N*E ≤ d^2) :
    lam*N*E^2 ≤ d^6 := by
  have hs := Real.sq_sqrt hN.le
  have H2 := pow_le_pow_left₀
    (mul_nonneg (Real.sqrt_nonneg N) hE.le) hupper 2
  have H : N*E^2 ≤ d^4 := by
    rw [mul_pow,hs] at H2
    nlinarith only [H2]
  have HH := mul_le_mul hld H
    (by positivity : 0 ≤ N*E^2) (sq_nonneg d)
  nlinarith only [HH]

theorem comparison_eq7_local_square_raw_gate_draft
    {N d E lam v : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hupper : Real.sqrt N*E ≤ d^2)
    (hv : comparisonSmallMass N E ≤ v) :
    lam*E ≤ d^6*v := by
  have hU := comparisonSmallMass_pos hN hE
  have h6 := comparison_eq7_lambda_energy_sixth_draft
    hN hd hE hlam hld hupper
  have HU := mul_le_mul_of_nonneg_right h6 hU.le
  have hident : lam*N*E^2*comparisonSmallMass N E = lam*E := by
    unfold comparisonSmallMass
    field_simp [hN.ne',hE.ne']
    <;> ring
  rw [hident] at HU
  exact HU.trans (mul_le_mul_of_nonneg_left hv (pow_nonneg hd.le 6))

theorem comparison_eq7_local_diameter_square_price_draft
    {N delta d E lam v L : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E)
    (hlam : 0 < lam) (hv : 0 < v)
    (hL : 0 ≤ L) (hraw : lam*E ≤ d^6*v) :
    lam*(16*v)*(144*L*E/(N^delta*d^3*v))^2 ≤
      331776*L^2*N^(-2*delta)*E := by
  have hNp : 0 < N^delta := Real.rpow_pos_of_pos hN _
  have hNp2 : 0 < N^(2*delta) := Real.rpow_pos_of_pos hN _
  have hden : 0 < N^(2*delta)*d^6*v := by positivity
  have hpow : (N^delta)^2=N^(2*delta) := by
    rw [←Real.rpow_mul_natCast hN.le]
    congr 1
    norm_num
    ring
  have H := mul_le_mul_of_nonneg_left hraw
    (show 0 ≤ 331776*L^2*E/(N^(2*delta)*d^6*v) by positivity)
  have hleft :
      (331776*L^2*E/(N^(2*delta)*d^6*v))*(lam*E) =
      lam*(16*v)*(144*L*E/(N^delta*d^3*v))^2 := by
    simp only [div_pow,mul_pow]
    rw [hpow]
    field_simp [hNp.ne',hNp2.ne',hd.ne',hv.ne']
    <;> ring
  have hright :
      (331776*L^2*E/(N^(2*delta)*d^6*v))*(d^6*v) =
      331776*L^2*N^(-2*delta)*E := by
    rw [show -2*delta = -(2*delta) by ring, Real.rpow_neg hN.le]
    field_simp [hNp2.ne',hd.ne',hv.ne']
    <;> ring
  rw [hleft,hright] at H
  exact H

theorem comparison_eq7_origin_radius_square_price_draft
    {N delta E lam A v r C : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (hA : 0 < A) (hC : 0 ≤ C)
    (Aeq : A = comparisonConditionalScale N delta E lam)
    (hUv : comparisonSmallMass N E ≤ v)
    (hvA : v ≤ C*A)
    (hr : 0 ≤ r) (hrU : r ≤ comparisonSmallMass N E)
    (hUA : comparisonSmallMass N E ≤ A) :
    lam*(16*v)*r^2 ≤ 16*C*N^(2*delta)*E := by
  let U := comparisonSmallMass N E
  have hUpos : 0 < U := comparisonSmallMass_pos hN hE
  have hv0 : 0 ≤ v := (hUpos.trans_le hUv).le
  have hr2 : r^2 ≤ U^2 := pow_le_pow_left₀ hr hrU 2
  have HU2 : U^2 ≤ A*U := by
    have H := mul_le_mul_of_nonneg_right hUA hUpos.le
    nlinarith only [H]
  have Hvr := mul_le_mul hvA hr2 (sq_nonneg r)
    (by positivity : 0 ≤ C*A)
  have HAU := mul_le_mul_of_nonneg_left HU2
    (show 0 ≤ C*A by positivity)
  have H := mul_le_mul_of_nonneg_left
    (show v*r^2 ≤ C*A^2*U by nlinarith only [Hvr,HAU])
    (show 0 ≤ 16*lam by positivity)
  have hcal : lam*A^2*U=N^(2*delta)*E := by
    rw [Aeq]
    exact comparison_conditional_small_mass_cost hN hE hlam
  calc
    lam*(16*v)*r^2 ≤ 16*lam*(C*A^2*U) := by
      convert H using 1 <;> ring
    _ = 16*C*(lam*A^2*U) := by ring
    _ = 16*C*N^(2*delta)*E := by rw [hcal]; ring

theorem comparison_eq7_ordinary_diameter_square_price_draft
    {N delta d E lam A v r C L : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hupper : Real.sqrt N*E ≤ d^2)
    (hA : 0 < A) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (Aeq : A = comparisonConditionalScale N delta E lam)
    (hUv : comparisonSmallMass N E ≤ v) (hvA : v ≤ C*A)
    (hr : 0 ≤ r) (hrU : r ≤ comparisonSmallMass N E)
    (hUA : comparisonSmallMass N E ≤ A) :
    lam*(16*v)*(144*L*E/(N^delta*d^3*v)+r)^2 ≤
      663552*L^2*N^(-2*delta)*E+
        32*C*N^(2*delta)*E := by
  have hv : 0 < v := (comparisonSmallMass_pos hN hE).trans_le hUv
  let Dloc := 144*L*E/(N^delta*d^3*v)
  have hDloc : 0 ≤ Dloc := by dsimp [Dloc]; positivity
  have hsq : (Dloc+r)^2 ≤ 2*(Dloc^2+r^2) := by
    nlinarith only [sq_nonneg (Dloc-r)]
  have Hsq := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ lam*(16*v) by positivity)
  have Hlocal := comparison_eq7_local_diameter_square_price_draft (delta := delta)
    hN hd hE hlam hv hL
    (comparison_eq7_local_square_raw_gate_draft hN hd hE hlam hld hupper hUv)
  have Hradius := comparison_eq7_origin_radius_square_price_draft
    hN hE hlam hA hC Aeq hUv hvA hr hrU hUA
  dsimp only [Dloc] at Hsq
  nlinarith only [Hsq,Hlocal,Hradius]

end OAI.SKFluctuations.LaplaceWindowFormalization
