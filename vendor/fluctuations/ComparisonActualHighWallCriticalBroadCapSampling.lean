module

public import ComparisonActualHighWallCriticalCapOriginCharge
public import ComparisonActualHighWallCriticalBroadBudgets

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualHighWallOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)
theorem criticalBroad_sampled_increment
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=a.data.rmin) (hrightContact : P.H c.right=0 ∨ c.right=1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ} (hij : i≤ j) (hj : j≤ as.length)
    (hiCap : a.shiftedNativeModel.R (partitionPoint 0 as i)∈Ioo c.left c.right)
    (hjCap : a.shiftedNativeModel.R (partitionPoint 0 as j)∈Ioo c.left c.right) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    physicalPathSecondMoment (n+1) steps (m.q 0) j-
      physicalPathSecondMoment (n+1) steps (m.q 0) i≤ a.criticalBroadMassDiameter+2*(mesh*Cnode) := by
  dsimp only
  let m:=a.shiftedNativeModel
  have hmass:=partitionPoint_mono as ho hij
  have hrad:=m.R_monotone hmass
  have hiHigh : m.u0≤ partitionPoint 0 as i:=by
    by_contra HH
    have H:=m.R_monotone (le_of_not_ge HH)
    rw [m.R_left] at H
    exact (not_lt_of_ge H) (c.hleft.trans_lt hiCap.1)
  have hjHigh : m.u0≤ partitionPoint 0 as j:=hiHigh.trans hmass
  have hi0 : 0< partitionPoint 0 as i := a.data.hs.1.trans
    (a.data.wallRadius_high_mass a.alpha (c.hleft.trans_lt hiCap.1))
  have hj0 : 0< partitionPoint 0 as j := hi0.trans_le hmass
  have hinc0:=c.critical_radiusS_increment_with_origin hN hlog hnd hleftContact hrightContact hiCap hjCap hrad
  have hinc : a.radiusS (m.R (partitionPoint 0 as j))-a.radiusS (m.R (partitionPoint 0 as i)) ≤ a.criticalBroadMassDiameter := by
    exact hinc0.trans (mul_le_mul_of_nonneg_left (show c.right-c.left+a.data.rmin ≤ a.data.rmin+a.cavityCapTravel by linarith [c.travel]) (show 0≤9*Real.log a.data.N by linarith))
  have herr:=physicalSampledNodeSecondMoment_increment_le n a.bf a.hf m.hbf m.hhf
    as ho he hmesh (hij.trans hj) hj hi0 hj0
  have hiSpec:=m.R_spec ⟨hiHigh,(partitionPoint_mem as ho i).2⟩
  have hjSpec:=m.R_spec ⟨hjHigh,(partitionPoint_mem as ho j).2⟩
  rw [←hiSpec,←hjSpec] at herr
  change physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) j-
    physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) i≤
      a.radiusS (m.R (partitionPoint 0 as j))-a.radiusS (m.R (partitionPoint 0 as i))+
        2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) m.q)) at herr
  exact herr.trans (add_le_add hinc le_rfl)

end ActualHighWallOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
