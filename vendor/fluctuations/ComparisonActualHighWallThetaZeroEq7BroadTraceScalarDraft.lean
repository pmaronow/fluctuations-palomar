module

public import ComparisonActualHighWallThetaZeroBroadTraceLoss
public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false

theorem comparison_eq7_broad_trace_ratio_at_small_scales_draft
    {N delta E lam e v K : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (he : 0 < e) (hK : 1 ≤ K)
    (hstrength : N^(-delta)*lam ≤ K*e)
    (hv : comparisonSmallMass N E ≤ v) :
    lam*(1+v/comparisonSmallMass N E)/(N*e*v) ≤
      2*K*N^delta*E := by
  have hU := comparisonSmallMass_pos hN hE
  have hvpos : 0 < v := hU.trans_le hv
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have H := comparison_conditional_broad_trace_cost hN hE hlam
    hstrength hv
  have hiden :
      lam*(1+v/comparisonSmallMass N E)/(N*e*v) =
        K*(lam*(1+v/comparisonSmallMass N E)/(N*(K*e)*v)) := by
    field_simp [hN.ne',he.ne',hvpos.ne',hKpos.ne',hU.ne']
  rw [hiden]
  have HH := mul_le_mul_of_nonneg_left H hKpos.le
  nlinarith only [HH]

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_inner_broad_loss_le_log_shape_draft
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hUv : comparisonSmallMass Q.data.N Q.data.E ≤ v)
    (hN : 1 ≤ Q.data.N) (hlog : 1 ≤ Real.log Q.data.N) :
    (32:ℝ)^2+Q.criticalBroadTraceLoss 4 v (min (4*v) 1)+1 ≤
      (criticalBroadOriginLossFactor*
        (1025+25*(1+Real.log (1+D^2))))*
      Real.log Q.data.N*
      (1+v/comparisonSmallMass Q.data.N Q.data.E) := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  let L := Real.log Q.data.N
  let Cr := 1+Real.log (1+D^2)
  let ratio := 1+v/U
  have hU : 0 < U := Q.data.hU
  have hratio : 1 ≤ ratio := by
    dsimp only [ratio]
    have H : 0 ≤ v/U := div_nonneg hv.le hU.le
    linarith only [H]
  have hCr : 1 ≤ Cr := by
    dsimp only [Cr]
    have HH := Real.log_nonneg
      (by nlinarith [sq_nonneg D] : (1:ℝ) ≤ 1+D^2)
    linarith only [HH]
  have hfactor : 0 ≤ criticalBroadOriginLossFactor :=
    criticalBroadOriginLossFactor_pos.le
  have Hlog := Q.criticalBroad_trace_log_le hN hlog
  have Hloss := Q.criticalBroad_loss_le hv hv1 hUv
  have Hprod := mul_le_mul_of_nonneg_left Hlog
    (show 0 ≤ 25*ratio by dsimp [ratio,U]; positivity)
  have Hconst : 1025 ≤ 1025*L*ratio := by
    have HL := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 1025*ratio by positivity)
    nlinarith only [HL,hratio]
  have Hshape : 1025+25*ratio*Real.log ((1+U)/U) ≤
      (1025+25*Cr)*L*ratio := by
    dsimp only [ratio,U,Cr,L] at Hprod ⊢
    nlinarith only [Hprod,Hconst]
  have Hscaled := mul_le_mul_of_nonneg_left Hshape hfactor
  exact Hloss.trans (by
    simpa only [U,L,Cr,ratio,mul_assoc] using Hscaled)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
