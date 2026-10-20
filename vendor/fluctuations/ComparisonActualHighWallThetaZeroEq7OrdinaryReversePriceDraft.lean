module

public import ComparisonConditionalErrorSize
public import ComparisonCanonicalPhysicalStrength

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_ordinary_local_reverse_linear_price_draft
    {N delta d E lam A v y Y L : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E)
    (hlam : 0 < lam) (hv : 0 < v) (hL : 0 ≤ L)
    (hY : 0 ≤ Y) (hy : 0 ≤ y) (hyA : y ≤ Y*A)
    (hprod : lam*A ≤ N^delta*d^3) :
    lam*(16*v)*(144*L*E/(N^delta*d^3*v))*y ≤
      2304*Y*L*E := by
  have hNp : 0 < N^delta := Real.rpow_pos_of_pos hN _
  have hYprod := mul_le_mul_of_nonneg_left hprod hY
  have hlamy := mul_le_mul_of_nonneg_left hyA hlam.le
  have hbound : lam*y ≤ Y*(N^delta*d^3) := by
    nlinarith only [hYprod,hlamy]
  have H := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ 2304*L*E/(N^delta*d^3) by positivity)
  have hleft :
      (2304*L*E/(N^delta*d^3))*(lam*y) =
      lam*(16*v)*(144*L*E/(N^delta*d^3*v))*y := by
    field_simp [hNp.ne',hd.ne',hv.ne']
    <;> ring
  have hright :
      (2304*L*E/(N^delta*d^3))*(Y*(N^delta*d^3)) =
      2304*Y*L*E := by
    field_simp [hNp.ne',hd.ne']
    <;> ring
  rw [hleft,hright] at H
  exact H

theorem comparison_eq7_ordinary_origin_reverse_linear_price_draft
    {N delta E lam A v r y C Y : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (hA : 0 < A) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (Aeq : A = comparisonConditionalScale N delta E lam)
    (hv : 0 ≤ v) (hvA : v ≤ C*A)
    (hr : 0 ≤ r) (hrU : r ≤ comparisonSmallMass N E)
    (hy : 0 ≤ y) (hyA : y ≤ Y*A) :
    lam*(16*v)*r*y ≤ 16*C*Y*N^(2*delta)*E := by
  let U := comparisonSmallMass N E
  have hUpos : 0 < U := comparisonSmallMass_pos hN hE
  have Hvr := mul_le_mul hvA hrU hr (by positivity : 0 ≤ C*A)
  have HvrY := mul_le_mul Hvr hyA hy
    (by positivity : 0 ≤ C*A*U)
  have H := mul_le_mul_of_nonneg_left
    (show v*r*y ≤ C*Y*A^2*U by nlinarith only [HvrY])
    (show 0 ≤ 16*lam by positivity)
  have hcal : lam*A^2*U=N^(2*delta)*E := by
    rw [Aeq]
    exact comparison_conditional_small_mass_cost hN hE hlam
  calc
    lam*(16*v)*r*y ≤ 16*lam*(C*Y*A^2*U) := by
      convert H using 1 <;> ring
    _ = 16*C*Y*(lam*A^2*U) := by ring
    _ = 16*C*Y*N^(2*delta)*E := by rw [hcal]; ring

theorem comparison_eq7_ordinary_reverse_price_of_interpolation_draft
    {N delta d E lam A v r y C Y L q eps rev : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hE : 0 < E)
    (hlam : 0 < lam) (hv : 0 < v) (hL : 0 ≤ L)
    (hA : 0 < A) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (Aeq : A = comparisonConditionalScale N delta E lam)
    (hvA : v ≤ C*A) (hr : 0 ≤ r)
    (hrU : r ≤ comparisonSmallMass N E)
    (hy : 0 ≤ y) (hyA : y ≤ Y*A)
    (hprod : lam*A ≤ N^delta*d^3)
    (hrev : rev ≤ (2*q)^4*
      (144*L*E/(N^delta*d^3*v)+r)*y*N^eps) :
    lam*(16*v)*rev ≤
      (2*q)^4*(2304*Y*L+16*C*Y*N^(2*delta))*N^eps*E := by
  let Dloc := 144*L*E/(N^delta*d^3*v)
  have hlocal := comparison_eq7_ordinary_local_reverse_linear_price_draft
    hN hd hE hlam hv hL hY hy hyA hprod
  have horigin := comparison_eq7_ordinary_origin_reverse_linear_price_draft
    hN hE hlam hA hC hY Aeq hv.le hvA hr hrU hy hyA
  have hfactor : 0 ≤ (2*q)^4*N^eps := by positivity
  have hweighted := mul_le_mul_of_nonneg_left hrev
    (show 0 ≤ lam*(16*v) by positivity)
  have hsum : lam*(16*v)*(Dloc+r)*y ≤
      (2304*Y*L+16*C*Y*N^(2*delta))*E := by
    dsimp only [Dloc]
    nlinarith only [hlocal,horigin]
  have H := mul_le_mul_of_nonneg_left hsum hfactor
  nlinarith only [H,hweighted]

end OAI.SKFluctuations.LaplaceWindowFormalization
