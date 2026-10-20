module

public import ComparisonActualHighWallThetaZeroCapLocalPhysical

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 11000000
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : W.Potential} (c : ShiftedCapInterval W P)

theorem radiusS_increment_local_with_origin
    (hN : 1≤W.data.N) (hlog : 1≤Real.log W.data.N) (hnd : 1/W.data.N≤W.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=W.data.rmin)
    (hrightContact : P.H c.right=0 ∨ c.right=1)
    {v K s t : ℝ} (hv : 0<v)
    (hleft : v≤W.alpha.val.val c.left+comparisonSmallMass W.data.N W.data.E)
    (hspan : W.alpha.val.val c.right-W.alpha.val.val c.left≤K*v)
    (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s≤t) :
    W.radiusS t-W.radiusS s≤W.localCapDiameter v K+W.data.rmin := by
  have H:=c.radiusS_increment_with_origin hN hlog hnd hleftContact hrightContact hs ht hst
  have HH:=mul_le_mul_of_nonneg_left (c.local_travel hv hleft hspan)
    (show 0≤9*Real.log W.data.N from by linarith)
  have hcharge : (if c.left=W.data.rmin then W.data.rmin else 0)≤W.data.rmin:=by
    split_ifs <;> linarith [W.data.hrbounds.1]
  have hD : 9*Real.log W.data.N*(c.right-c.left)≤W.localCapDiameter v K:=by
    simpa only [localCapDiameter,mul_div_assoc,mul_assoc] using HH
  linarith only [H,hD,hcharge]

theorem sampled_increment_local_with_origin
    (hN : 1≤W.data.N) (hlog : 1≤Real.log W.data.N) (hnd : 1/W.data.N≤W.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=W.data.rmin)
    (hrightContact : P.H c.right=0 ∨ c.right=1)
    {v K : ℝ} (hv : 0<v)
    (hleft : v≤W.alpha.val.val c.left+comparisonSmallMass W.data.N W.data.E)
    (hspan : W.alpha.val.val c.right-W.alpha.val.val c.left≤K*v)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ} (hij : i≤j) (hj : j≤as.length)
    (hiCap : W.shiftedNativeModel.R (partitionPoint 0 as i)∈Ioo c.left c.right)
    (hjCap : W.shiftedNativeModel.R (partitionPoint 0 as j)∈Ioo c.left c.right) :
    let m:=W.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    physicalPathSecondMoment (n+1) steps (m.q 0) j-
      physicalPathSecondMoment (n+1) steps (m.q 0) i≤
        W.localCapDiameter v K+W.data.rmin+2*(mesh*Cnode) := by
  dsimp only
  let m:=W.shiftedNativeModel
  have hmass:=partitionPoint_mono as ho hij
  have hrad:=m.R_monotone hmass
  have hiHigh : m.u0≤partitionPoint 0 as i:=by
    by_contra HH
    have H:=m.R_monotone (le_of_not_ge HH)
    rw [m.R_left] at H
    exact (not_lt_of_ge H) (c.hleft.trans_lt hiCap.1)
  have hjHigh : m.u0≤partitionPoint 0 as j:=hiHigh.trans hmass
  have hi0 : 0<partitionPoint 0 as i:=W.data.hs.1.trans_le hiHigh
  have hj0 : 0<partitionPoint 0 as j:=W.data.hs.1.trans_le hjHigh
  have hinc:=c.radiusS_increment_local_with_origin hN hlog hnd hleftContact hrightContact
    hv hleft hspan hiCap hjCap hrad
  have herr:=physicalSampledNodeSecondMoment_increment_le n W.sweepBf W.sweepHf m.hbf m.hhf
    as ho he hmesh (hij.trans hj) hj hi0 hj0
  have hiSpec:=m.R_spec ⟨hiHigh,(partitionPoint_mem as ho i).2⟩
  have hjSpec:=m.R_spec ⟨hjHigh,(partitionPoint_mem as ho j).2⟩
  rw [←hiSpec,←hjSpec] at herr
  change physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) j-
    physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) i≤
      W.radiusS (m.R (partitionPoint 0 as j))-W.radiusS (m.R (partitionPoint 0 as i))+
        2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) m.q)) at herr
  exact herr.trans (add_le_add hinc le_rfl)

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
