module

public import ComparisonActualHighWallThetaZeroEq7BroadTracePriceDraft
public import ComparisonActualHighWallThetaZeroEq7BroadGeometryPriceDraft
public import ComparisonActualHighWallThetaZeroEq7ExactBudgetNormalizationDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

def comparisonEq7BroadPieceConstant
    (K Kloss beta Tbeta C J Y q : ℝ) : ℝ :=
  2*K*Kloss*(20736*beta+3456*Tbeta)+
  8*C*(76+64*beta)*J^2+256*C*(2*q)^4*J*Y+16

theorem comparison_eq7_broad_piece_of_all_atoms_draft
    {N delta eps E lam A U P v loss K Kloss L beta Tbeta C J Y
      width Db y q rev cut : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (hE : 0 < E) (hlam : 0 < lam)
    (hA : 0 < A) (hU : 0 < U) (hUA : U ≤ A)
    (hP : 0 < P) (hv : 0 < v)
    (hloss : 0 ≤ loss) (hK : 0 ≤ K) (hKloss : 0 ≤ Kloss)
    (hL : 1 ≤ L) (hbeta : 0 ≤ beta) (hTbeta : 0 ≤ Tbeta)
    (hTbetaBound : comparisonEq7BroadTemperatureConstant beta ≤ Tbeta)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hY : 0 ≤ Y)
    (hwidth : 0 ≤ width) (hwidthV : width ≤ 4*v)
    (hwidthA : width ≤ 8*C*A)
    (hDb : 0 ≤ Db) (hDbU : Db ≤ J*L^2*U)
    (hy : 0 ≤ y) (hyA : y ≤ Y*A)
    (hcal : lam*A^2*U=N^(2*delta)*E)
    (htrace : lam*loss/(P*v) ≤ 2*K*Kloss*L*N^delta*E)
    (hlogCut : Real.log (width/cut) ≤ beta*L)
    (hrev : rev ≤ (2*q)^4*Db*y*N^eps)
    (hcut : lam*cut ≤ E) :
    let T := 66+64*(beta*L)+65536*(1+beta*L)^2
    let side := 48*(108*loss*L^2/(P*(v/4))*Real.log (width/cut))
    let diameter := (76+64*beta*L)*width*Db^2
    let reverse := 32*width*rev
    let covariance := T*(54*loss*L^2*width/(P*(v/4)^2))
    let cutoff := 16*cut
    lam*(side+diameter+reverse+covariance+cutoff) ≤
      comparisonEq7BroadPieceConstant K Kloss beta Tbeta C J Y q*
        L^5*N^(2*delta+eps)*E := by
  let T := 66+64*(beta*L)+65536*(1+beta*L)^2
  let side := 48*(108*loss*L^2/(P*(v/4))*Real.log (width/cut))
  let diameter := (76+64*beta*L)*width*Db^2
  let reverse := 32*width*rev
  let covariance := T*(54*loss*L^2*width/(P*(v/4)^2))
  let cutoff := 16*cut
  let X := N^(2*delta+eps)*E
  let Ks := 2*K*Kloss*20736*beta
  let Kd := 8*C*(76+64*beta)*J^2
  let Kr := 256*C*(2*q)^4*J*Y
  let Kc := 2*K*Kloss*3456*Tbeta
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hKs : 0 ≤ Ks := by dsimp [Ks]; positivity
  have hKd : 0 ≤ Kd := by dsimp [Kd]; positivity
  have hKr : 0 ≤ Kr := by dsimp [Kr]; positivity
  have hKc : 0 ≤ Kc := by dsimp [Kc]; positivity
  have hT := (comparison_eq7_broad_temperature_bound_draft hbeta hL)
  have Hside := comparison_eq7_broad_side_trace_price_draft
    hNp hE hlam hP hv hloss hKloss hK hL hbeta hlogCut htrace
  have hTupper : T ≤ Tbeta*L^2 :=
    hT.2.trans (mul_le_mul_of_nonneg_right hTbetaBound (sq_nonneg L))
  have Hcov := comparison_eq7_broad_covariance_trace_price_draft
    (beta:=beta)
    hNp hE hlam hP hv hloss hKloss hK hL hT.1 hTbeta
    hwidthV hTupper htrace
  have Hdiam := comparison_eq7_broad_diameter_square_price_draft
    hNp hE hlam hA hU hUA hC hJ hL hbeta hwidth hwidthA
    hDb hDbU hcal
  have Hrev := comparison_eq7_broad_reverse_price_draft
    hNp hE hlam hA hU hC hY hJ (by linarith only [hL])
    hwidth hwidthA hDb hDbU hy hyA hcal hrev
  have Hcut := mul_le_mul_of_nonneg_left hcut
    (by norm_num : (0:ℝ) ≤ 16)
  have hPow (t : ℝ) (ht : t ≤ 2*delta+eps) :
      N^t*E ≤ X := by
    have H := Real.rpow_le_rpow_of_exponent_le hN ht
    dsimp only [X]
    exact mul_le_mul_of_nonneg_right H hE.le
  have HL3 : 1 ≤ L^3 := by
    simpa using (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL 3)
  have Hside' : lam*side ≤ Ks*L^5*X := by
    have H := mul_le_mul_of_nonneg_left
      (hPow delta (by linarith only [hdelta,heps]))
      (show 0 ≤ Ks*L^5 by positivity)
    dsimp only [side,Ks,X] at *
    nlinarith only [Hside,H]
  have Hcov' : lam*covariance ≤ Kc*L^5*X := by
    have H := mul_le_mul_of_nonneg_left
      (hPow delta (by linarith only [hdelta,heps]))
      (show 0 ≤ Kc*L^5 by positivity)
    dsimp only [covariance,T,Kc,X] at *
    nlinarith only [Hcov,H]
  have Hdiam' : lam*diameter ≤ Kd*L^5*X := by
    have H := mul_le_mul_of_nonneg_left
      (hPow (2*delta) (by linarith only [heps]))
      (show 0 ≤ Kd*L^5 by positivity)
    dsimp only [diameter,Kd,X] at *
    nlinarith only [Hdiam,H]
  have Hrev' : lam*reverse ≤ Kr*L^5*X := by
    have H := mul_le_mul_of_nonneg_left HL3
      (show 0 ≤ Kr*L^2*X by positivity)
    dsimp only [reverse,Kr,X] at *
    nlinarith only [Hrev,H]
  have Hcut' : lam*cutoff ≤ 16*L^5*X := by
    have hEtoX := hPow 0 (by linarith only [hdelta,heps])
    simp only [Real.rpow_zero,one_mul] at hEtoX
    have H := mul_le_mul_of_nonneg_left hEtoX
      (show 0 ≤ 16*L^5 by positivity)
    have HL5 : 1 ≤ L^5 := by
      simpa using (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL 5)
    have HE := mul_le_mul_of_nonneg_right HL5 hE.le
    dsimp only [cutoff,X] at *
    nlinarith only [Hcut,HE,H]
  have H := comparison_eq7_broad_literal_components_draft
    hL hX hKs hKd hKr hKc (by norm_num : (0:ℝ) ≤ 16)
    Hside' Hdiam' Hrev' Hcov' Hcut'
  dsimp only [comparisonEq7BroadPieceConstant,Ks,Kd,Kr,Kc,X,
    side,diameter,reverse,covariance,cutoff,T] at H ⊢
  convert H using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
