module

public import ComparisonActualHighWallThetaZeroBroadTraceLoss
public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_inner_broad_diameter_le_small_mass_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ Q.data.N) (hdelta : 0 ≤ delta)
    (hlog : 1 ≤ Real.log Q.data.N) :
    Q.criticalBroadMassDiameter ≤
      9*(2+Real.log (1+D^2))*(Real.log Q.data.N)^2*
        comparisonSmallMass Q.data.N Q.data.E := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  let L := Real.log Q.data.N
  let Lcap := comparisonConstraintLength Q.data.N Q.data.E Q.data.d
  let Cr := 1+Real.log (1+D^2)
  have hU : 0 < U := Q.data.hU
  have hL : 1 ≤ L := hlog
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hL2 : L ≤ L^2 := by nlinarith only [hL,sq_nonneg (L-1)]
  have hCr : 0 ≤ Cr := by
    dsimp only [Cr]
    have H := Real.log_nonneg
      (by nlinarith [sq_nonneg D] : (1:ℝ) ≤ 1+D^2)
    linarith only [H]
  have hcap0 : 0 ≤ Lcap := Q.data.hL.le
  have hcapU : Lcap ≤ U := by
    dsimp only [Lcap,comparisonConstraintLength]
    exact min_le_left _ _
  have hNpow : 1 ≤ Q.data.N^delta := Real.one_le_rpow hN hdelta
  have hNpowPos : 0 < Q.data.N^delta :=
    Real.rpow_pos_of_pos Q.data.hN _
  have hcapRatio : Lcap/Q.data.N^delta ≤ U := by
    apply (div_le_iff₀ hNpowPos).mpr
    have H := mul_le_mul_of_nonneg_left hNpow hU.le
    nlinarith only [hcapU,H]
  have hlogU : Real.log ((1+U)/U) ≤ Cr*L := by
    simpa only [U,L,Cr] using Q.criticalBroad_trace_log_le hN hlog
  have hlogU0 : 0 ≤ Real.log ((1+U)/U) := by
    apply Real.log_nonneg
    exact (one_le_div hU).mpr (by linarith only [hU])
  have htravel : Q.cavityCapTravel ≤ U*Cr*L := by
    have H := mul_le_mul hcapRatio hlogU hlogU0 hU.le
    simpa only [cavityCapTravel,U,Lcap,Cr,L,mul_assoc] using H
  have hr : Q.data.rmin ≤ U := Q.radius_le_smallMass
  have hUL := mul_le_mul_of_nonneg_left hL2 hU.le
  have hsum :
      9*L*(Q.data.rmin+Q.cavityCapTravel) ≤
        9*(1+Cr)*L^2*U := by
    have H := mul_le_mul_of_nonneg_left (add_le_add hr htravel)
      (by positivity : (0:ℝ) ≤ 9*L)
    have Hsmall := mul_le_mul_of_nonneg_left hUL
      (by norm_num : (0:ℝ) ≤ 9)
    calc
      _ ≤ 9*L*(U+U*Cr*L) := H
      _ = 9*(U*L)+9*Cr*U*L^2 := by ring
      _ ≤ 9*(U*L^2)+9*Cr*U*L^2 := add_le_add Hsmall (le_refl _)
      _ = _ := by ring
  simpa only [criticalBroadMassDiameter,Cr,L,U,
    show 1+(1+Real.log (1+D^2)) =
      2+Real.log (1+D^2) by ring] using hsum

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
