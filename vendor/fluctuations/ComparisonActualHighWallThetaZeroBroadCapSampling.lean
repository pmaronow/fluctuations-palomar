module

public import ComparisonActualHighWallThetaZeroCapOscillation
public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonActualHighWallCriticalBroadCapSampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (c : ShiftedCapInterval Q P)

theorem criticalBroad_sampled_increment
    (hN : 1≤ Q.data.N) (hlog : 1≤ Real.log Q.data.N) (hnd : 1/Q.data.N≤ Q.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=Q.data.rmin) (hrightContact : P.H c.right=0 ∨ c.right=1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ} (hij : i≤ j) (hj : j≤ as.length)
    (hiCap : Q.shiftedNativeModel.R (partitionPoint 0 as i)∈Ioo c.left c.right)
    (hjCap : Q.shiftedNativeModel.R (partitionPoint 0 as j)∈Ioo c.left c.right) :
    let m:=Q.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    physicalPathSecondMoment (n+1) steps (m.q 0) j-
      physicalPathSecondMoment (n+1) steps (m.q 0) i≤ Q.criticalBroadMassDiameter+2*(mesh*Cnode) := by
  dsimp only
  let m:=Q.shiftedNativeModel
  have hmass:=partitionPoint_mono as ho hij
  have hrad:=m.R_monotone hmass
  have hiHigh : m.u0≤ partitionPoint 0 as i:=by
    by_contra HH
    have H:=m.R_monotone (le_of_not_ge HH)
    rw [m.R_left] at H
    exact (not_lt_of_ge H) (c.hleft.trans_lt hiCap.1)
  have hjHigh : m.u0≤ partitionPoint 0 as j:=hiHigh.trans hmass
  have hi0 : 0< partitionPoint 0 as i := Q.data.hs.1.trans
    (Q.data.wallRadius_high_mass Q.alpha (c.hleft.trans_lt hiCap.1))
  have hj0 : 0< partitionPoint 0 as j := hi0.trans_le hmass
  have hinc0:=c.radiusS_increment_with_origin hN hlog hnd hleftContact hrightContact hiCap hjCap hrad
  have hinc : Q.radiusS (m.R (partitionPoint 0 as j))-Q.radiusS (m.R (partitionPoint 0 as i)) ≤ Q.criticalBroadMassDiameter := by
    have hw:(if c.left=Q.data.rmin then Q.data.rmin else 0)≤Q.data.rmin:=by
      split_ifs <;> linarith [Q.data.hrbounds.1]
    have hwlog:Q.data.rmin≤9*Real.log Q.data.N*Q.data.rmin:=by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)≤9*Real.log Q.data.N) Q.data.hrbounds.1.le
    have htravel:=c.travel
    have htravelLog := mul_le_mul_of_nonneg_left htravel
      (show 0 ≤ 9*Real.log Q.data.N by linarith)
    dsimp only [criticalBroadMassDiameter]
    nlinarith only [hinc0,hw,hwlog,htravelLog]
  have herr:=physicalSampledNodeSecondMoment_increment_le n Q.sweepBf Q.sweepHf m.hbf m.hhf
    as ho he hmesh (hij.trans hj) hj hi0 hj0
  have hiSpec:=m.R_spec ⟨hiHigh,(partitionPoint_mem as ho i).2⟩
  have hjSpec:=m.R_spec ⟨hjHigh,(partitionPoint_mem as ho j).2⟩
  rw [←hiSpec,←hjSpec] at herr
  change physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) j-
    physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) i≤
      Q.radiusS (m.R (partitionPoint 0 as j))-Q.radiusS (m.R (partitionPoint 0 as i))+
        2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) m.q)) at herr
  exact herr.trans (add_le_add hinc le_rfl)
end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
