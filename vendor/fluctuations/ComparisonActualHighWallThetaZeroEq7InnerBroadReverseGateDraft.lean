module

public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonPhysicalCapScale
public import ComparisonReverseInterpolationSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 9000000

theorem comparison_positive_origin_broad_reverse_ratio
    {N delta U Lcap rmin y : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hU : 0 < U) (hU1 : U ≤ 1)
    (hL : N^(-(1:ℝ)) ≤ Lcap)
    (hrmin : 0 ≤ rmin)
    (hy : 0 ≤ y) (hyN : y ≤ N^(6+delta)) :
    y/(9*Real.log N*(rmin+
        (Lcap/N^delta)*Real.log ((1+U)/U))) ≤
      N^(7+2*delta) := by
  let travel := (Lcap/N^delta)*Real.log ((1+U)/U)
  let diam := 9*Real.log N*(rmin+travel)
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNpow : 0 < N^delta := Real.rpow_pos_of_pos hNp _
  have hLpos : 0 < Lcap := (Real.rpow_pos_of_pos hNp _).trans_le hL
  have hLogU : 0 < Real.log ((1+U)/U) :=
    Real.log_pos ((lt_div_iff₀ hU).mpr (by linarith))
  have htravel : 0 < travel := mul_pos (div_pos hLpos hNpow) hLogU
  have hdiam : 0 < diam := by
    dsimp only [diam]
    positivity
  have hcoeff := comparison_cap_log_coefficient_lower hlog hU hU1
  have H1 := mul_le_mul_of_nonneg_right hcoeff
    (div_nonneg hLpos.le hNpow.le)
  have H2 := div_le_div_of_nonneg_right hL hNpow.le
  have hpower : N^(-(1:ℝ))/N^delta = N^(-(delta+1)) := by
    rw [←Real.rpow_sub hNp]
    congr 1
    ring
  have hDlow : N^(-(delta+1)) ≤ diam := by
    rw [hpower] at H2
    dsimp only [diam,travel]
    have H3 := mul_le_mul_of_nonneg_left
      (show (Lcap/N^delta)*Real.log ((1+U)/U) ≤
        rmin+(Lcap/N^delta)*Real.log ((1+U)/U) by linarith only [hrmin])
      (show 0≤9*Real.log N by linarith)
    nlinarith only [H1,H2,H3]
  have H := comparison_reverse_ratio_of_scales hNp hdiam hy hDlow hyN
  have hexp : (delta+1)+(6+delta)=7+2*delta := by ring
  simpa only [diam,travel,hexp] using H

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem eq7_inner_broad_reverse_ratio_of_raw_gate
    (hN : 1 ≤ Q.data.N) (hlog : 1 ≤ Real.log Q.data.N)
    (hL : Q.data.N^(-(1:ℝ)) ≤
      comparisonConstraintLength Q.data.N Q.data.E Q.data.d)
    {v : ℝ} (hv : 0 ≤ v)
    (hy : Q.criticalBroadMassHeight v ≤ Q.data.N^(6+delta)) :
    Q.criticalBroadMassHeight v/Q.criticalBroadMassDiameter ≤
      Q.data.N^(7+2*delta) := by
  have hU1 : comparisonSmallMass Q.data.N Q.data.E ≤ 1 :=
    Q.data.hsmall.trans Q.data.hd1
  have hy0 : 0 ≤ Q.criticalBroadMassHeight v :=
    Q.criticalBroadMassHeight_nonneg hv
  have H := comparison_positive_origin_broad_reverse_ratio hN hlog
    Q.data.hU hU1 hL Q.data.hrbounds.1.le hy0 hy
  simpa only [criticalBroadMassDiameter,cavityCapTravel] using H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
