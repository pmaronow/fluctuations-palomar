module

public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_broad_diameter_square_price_draft
    {N delta E lam A U C J L beta width Db : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (hA : 0 < A) (hU : 0 < U) (hUA : U ≤ A)
    (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hL : 1 ≤ L) (hbeta : 0 ≤ beta)
    (hwidth : 0 ≤ width) (hwidthA : width ≤ 8*C*A)
    (hDb : 0 ≤ Db) (hDbU : Db ≤ J*L^2*U)
    (hcal : lam*A^2*U=N^(2*delta)*E) :
    lam*(76+64*beta*L)*width*Db^2 ≤
      8*C*(76+64*beta)*J^2*L^5*N^(2*delta)*E := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hcoef : 76+64*beta*L ≤ (76+64*beta)*L := by
    nlinarith only [hL]
  have hcoef0 : 0 ≤ (76+64*beta)*L := by positivity
  have Hcw := mul_le_mul hcoef hwidthA hwidth hcoef0
  have HD2 := pow_le_pow_left₀ hDb hDbU 2
  have Hprod := mul_le_mul Hcw HD2 (sq_nonneg Db)
    (by positivity : 0 ≤ (76+64*beta)*L*(8*C*A))
  have Hlambda := mul_le_mul_of_nonneg_left Hprod hlam.le
  have HU2 : U^2 ≤ A*U := by
    have H := mul_le_mul_of_nonneg_right hUA hU.le
    nlinarith only [H]
  have HU := mul_le_mul_of_nonneg_left HU2
    (show 0 ≤ lam*A by positivity)
  have Hcal := mul_le_mul_of_nonneg_left HU
    (show 0 ≤ 8*C*(76+64*beta)*J^2*L^5 by positivity)
  have hcalEq : (lam*A)*(A*U)=N^(2*delta)*E := by
    nlinarith only [hcal]
  rw [hcalEq] at Hcal
  nlinarith only [Hlambda,Hcal]

theorem comparison_eq7_broad_reverse_price_draft
    {N delta eps E lam A U C Y J L width Db y q rev : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (hA : 0 < A) (hU : 0 < U)
    (hC : 0 ≤ C) (hY : 0 ≤ Y) (hJ : 0 ≤ J)
    (hL : 0 ≤ L)
    (hwidth : 0 ≤ width) (hwidthA : width ≤ 8*C*A)
    (hDb : 0 ≤ Db) (hDbU : Db ≤ J*L^2*U)
    (hy : 0 ≤ y) (hyA : y ≤ Y*A)
    (hcal : lam*A^2*U=N^(2*delta)*E)
    (hrev : rev ≤ (2*q)^4*Db*y*N^eps) :
    lam*(32*width)*rev ≤
      256*C*(2*q)^4*J*Y*L^2*N^(2*delta+eps)*E := by
  have Hwd := mul_le_mul hwidthA hDbU hDb
    (by positivity : 0 ≤ 8*C*A)
  have Hwdy := mul_le_mul Hwd hyA hy
    (by positivity : 0 ≤ (8*C*A)*(J*L^2*U))
  have Hgeom : width*Db*y ≤ 8*C*J*Y*L^2*A^2*U := by
    nlinarith only [Hwdy]
  have hfactor : 0 ≤ lam*32*(2*q)^4*N^eps := by positivity
  have Hprice := mul_le_mul_of_nonneg_left Hgeom hfactor
  have Hrev := mul_le_mul_of_nonneg_left hrev
    (show 0 ≤ lam*(32*width) by positivity)
  have hpow : N^(2*delta)*N^eps = N^(2*delta+eps) :=
    (Real.rpow_add hN (2*delta) eps).symm
  have Hcal :
      (256*C*(2*q)^4*J*Y*L^2*N^eps)*(lam*A^2*U) =
        256*C*(2*q)^4*J*Y*L^2*N^(2*delta+eps)*E := by
    rw [hcal]
    calc
      _ = 256*C*(2*q)^4*J*Y*L^2*(N^(2*delta)*N^eps)*E := by ring
      _ = _ := by rw [hpow]
  nlinarith only [Hprice,Hrev,Hcal]

end OAI.SKFluctuations.LaplaceWindowFormalization
