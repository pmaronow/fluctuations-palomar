module

public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

def comparisonEq7BroadTemperatureConstant (beta : ℝ) : ℝ :=
  66+64*beta+65536*(1+beta)^2

theorem comparison_eq7_broad_temperature_bound_draft
    {beta L : ℝ} (hbeta : 0 ≤ beta) (hL : 1 ≤ L) :
    0 ≤ 66+64*(beta*L)+65536*(1+beta*L)^2 ∧
    66+64*(beta*L)+65536*(1+beta*L)^2 ≤
      comparisonEq7BroadTemperatureConstant beta*L^2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL2 : 1 ≤ L^2 := by
    nlinarith only [hL,sq_nonneg (L-1)]
  have hLL2 : L ≤ L^2 := by
    nlinarith only [hL,sq_nonneg (L-1)]
  have hbetaL : 0 ≤ beta*L := mul_nonneg hbeta hL0
  have hsum : 1+beta*L ≤ (1+beta)*L := by
    nlinarith only [hL]
  have hsq := pow_le_pow_left₀ (by linarith only [hbetaL] :
    0 ≤ 1+beta*L) hsum 2
  have h1 : 66 ≤ 66*L^2 := by nlinarith only [hL2]
  have h2 : 64*beta*L ≤ 64*beta*L^2 := by
    have H := mul_le_mul_of_nonneg_left hLL2
      (show 0 ≤ 64*beta by positivity)
    nlinarith only [H]
  constructor
  · positivity
  · unfold comparisonEq7BroadTemperatureConstant
    nlinarith only [hsq,h1,h2]

theorem comparison_eq7_broad_loss_trace_product_draft
    {N delta E lam P v U loss Kloss K L : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (hP : 0 < P) (hv : 0 < v) (hU : 0 < U)
    (hKloss : 0 ≤ Kloss) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hloss : loss ≤ Kloss*L*(1+v/U))
    (htrace : lam*(1+v/U)/(P*v) ≤ 2*K*N^delta*E) :
    lam*loss/(P*v) ≤ 2*K*Kloss*L*N^delta*E := by
  have hden : 0 < P*v := mul_pos hP hv
  have H1 := mul_le_mul_of_nonneg_left hloss
    (div_nonneg hlam.le hden.le)
  have H2 := mul_le_mul_of_nonneg_left htrace
    (show 0 ≤ Kloss*L by positivity)
  calc
    lam*loss/(P*v) = (lam/(P*v))*loss := by ring
    _ ≤ (lam/(P*v))*(Kloss*L*(1+v/U)) := H1
    _ = (Kloss*L)*(lam*(1+v/U)/(P*v)) := by ring
    _ ≤ (Kloss*L)*(2*K*N^delta*E) := H2
    _ = _ := by ring

theorem comparison_eq7_broad_side_trace_price_draft
    {N delta E lam P v loss Kloss K L beta width cut : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (hP : 0 < P) (hv : 0 < v)
    (hloss : 0 ≤ loss) (hKloss : 0 ≤ Kloss) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hbeta : 0 ≤ beta)
    (hlog : Real.log (width/cut) ≤ beta*L)
    (htraceLoss : lam*loss/(P*v) ≤
      2*K*Kloss*L*N^delta*E) :
    lam*(48*(108*loss*L^2/(P*(v/4))*
      Real.log (width/cut))) ≤
      (2*K*Kloss*20736*beta)*L^5*N^delta*E := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hden : 0 < P*(v/4) := by positivity
  have hcoef : 0 ≤ lam*48*108*loss*L^2/(P*(v/4)) := by positivity
  have Hlog := mul_le_mul_of_nonneg_left hlog hcoef
  have hcoefEq :
      lam*48*108*loss*L^2/(P*(v/4)) =
      lam*20736*loss*L^2/(P*v) := by
    field_simp [hP.ne',hv.ne']
    <;> ring
  rw [hcoefEq] at Hlog
  have heq :
      lam*(48*(108*loss*L^2/(P*(v/4))*
        Real.log (width/cut))) =
      lam*20736*loss*L^2/(P*v)*Real.log (width/cut) := by
    field_simp [hP.ne',hv.ne']
    <;> ring
  have Htrace := mul_le_mul_of_nonneg_left htraceLoss
    (show 0 ≤ 20736*beta*L^3 by positivity)
  have hL45 : L^4 ≤ L^5 := by
    nlinarith only [hL, mul_nonneg (pow_nonneg hL0 4)
      (sub_nonneg.mpr hL)]
  have Hlast := mul_le_mul_of_nonneg_left hL45
    (show 0 ≤ 2*K*Kloss*20736*beta*N^delta*E by positivity)
  rw [heq]
  calc
    lam*20736*loss*L^2/(P*v)*Real.log (width/cut) ≤
        lam*20736*loss*L^2/(P*v)*(beta*L) := Hlog
    _ = (20736*beta*L^3)*(lam*loss/(P*v)) := by ring
    _ ≤ (20736*beta*L^3)*(2*K*Kloss*L*N^delta*E) := Htrace
    _ = (2*K*Kloss*20736*beta*N^delta*E)*L^4 := by ring
    _ ≤ (2*K*Kloss*20736*beta*N^delta*E)*L^5 := Hlast
    _ = _ := by ring

theorem comparison_eq7_broad_covariance_trace_price_draft
    {N delta E lam P v loss Kloss K L beta width T Tbeta : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (hP : 0 < P) (hv : 0 < v)
    (hloss : 0 ≤ loss) (hKloss : 0 ≤ Kloss) (hK : 0 ≤ K)
    (hL : 1 ≤ L) (hT0 : 0 ≤ T) (hTbeta : 0 ≤ Tbeta)
    (hwidth : width ≤ 4*v)
    (hT : T ≤ Tbeta*L^2)
    (htraceLoss : lam*loss/(P*v) ≤
      2*K*Kloss*L*N^delta*E) :
    lam*(T*(54*loss*L^2*width/(P*(v/4)^2))) ≤
      (2*K*Kloss*3456*Tbeta)*L^5*N^delta*E := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hden : 0 < P*(v/4)^2 := by positivity
  have hcoef : 0 ≤ lam*T*54*loss*L^2/(P*(v/4)^2) := by positivity
  have Hw := mul_le_mul_of_nonneg_left hwidth hcoef
  have heqLeft :
      lam*(T*(54*loss*L^2*width/(P*(v/4)^2))) =
      (lam*T*54*loss*L^2/(P*(v/4)^2))*width := by ring
  have heqRight :
      (lam*T*54*loss*L^2/(P*(v/4)^2))*(4*v) =
      T*(3456*L^2)*(lam*loss/(P*v)) := by
    field_simp [hP.ne',hv.ne']
    <;> ring
  rw [←heqLeft,heqRight] at Hw
  have Ht := mul_le_mul_of_nonneg_right hT
    (show 0 ≤ 3456*L^2*(lam*loss/(P*v)) by positivity)
  have Htrace := mul_le_mul_of_nonneg_left htraceLoss
    (show 0 ≤ 3456*Tbeta*L^4 by positivity)
  nlinarith only [Hw,Ht,Htrace]

end OAI.SKFluctuations.LaplaceWindowFormalization
