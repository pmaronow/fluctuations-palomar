module

public import ComparisonActualHighOnlyCapSampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def chosenLocalCapDiameter
    (a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (v K : ℝ) : ℝ :=
  9*Real.log a.data.N*K*a.data.E/(a.data.N^delta*a.data.d^3*v)

namespace ShiftedCapInterval
variable {P : a.Potential} (c : ShiftedCapInterval a P)

theorem local_radius_travel {v K : ℝ} (hv : 0 < v)
    (hleft : v ≤ a.alpha.val.val c.left+a.data.U)
    (hspan : a.alpha.val.val c.right-a.alpha.val.val c.left ≤ K*v) :
    c.right-c.left ≤ K*a.data.E/(a.data.N^delta*a.data.d^3*v) := by
  have ht:=(P.cap_interval_travel c.hleft c.hlt.le c.hright c.negative).2.2 v hv hleft
  have hh:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hspan a.data.hE.le)
    (show 0 ≤ a.data.N^delta*a.data.d^3*v^2 from
      mul_nonneg (mul_nonneg (Real.rpow_nonneg a.data.hN.le _) (pow_nonneg a.data.hd.le _))
        (sq_nonneg _))
  exact ht.trans (by convert hh using 1;field_simp)

theorem radiusS_increment_local_chosen
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=0) (hrightContact : P.H c.right=0 ∨ c.right=1)
    {v K s t : ℝ} (hv : 0 < v)
    (hleft : v ≤ a.alpha.val.val c.left+a.data.U)
    (hspan : a.alpha.val.val c.right-a.alpha.val.val c.left ≤ K*v)
    (hs : s∈Ioo c.left c.right) (ht : t∈Ioo c.left c.right) (hst : s ≤ t) :
    a.radiusS t-a.radiusS s ≤ a.chosenLocalCapDiameter v K := by
  have H:=c.radiusS_increment_all hN hlog hnd hleftContact hrightContact hs ht hst
  have HH:=mul_le_mul_of_nonneg_left (c.local_radius_travel hv hleft hspan)
    (show 0 ≤ 9*Real.log a.data.N by linarith)
  exact H.trans (by simpa only [chosenLocalCapDiameter,mul_div_assoc,mul_assoc] using HH)

theorem sampled_increment_at_diameter
    {diameter : ℝ}
    (hinc : ∀s∈Ioo c.left c.right,∀t∈Ioo c.left c.right,s ≤ t →
      a.radiusS t-a.radiusS s ≤ diameter)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ as.length)
    (hiCap : a.shiftedNativeModel.R (partitionPoint 0 as i)∈Ioo c.left c.right)
    (hjCap : a.shiftedNativeModel.R (partitionPoint 0 as j)∈Ioo c.left c.right) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    physicalPathSecondMoment (n+1) steps (m.q 0) j-
      physicalPathSecondMoment (n+1) steps (m.q 0) i ≤ diameter+2*(mesh*Cnode) := by
  dsimp only
  let m:=a.shiftedNativeModel
  have hmass:=partitionPoint_mono as ho hij
  have hrad:=m.R_monotone hmass
  have hiHigh : m.u0 ≤ partitionPoint 0 as i:=by
    by_contra HH
    have H:=m.R_monotone (le_of_not_ge HH)
    rw [m.R_left] at H
    exact (not_lt_of_ge H) (c.hleft.trans_lt hiCap.1)
  have hjHigh : m.u0 ≤ partitionPoint 0 as j:=hiHigh.trans hmass
  have hi0 : 0 < partitionPoint 0 as i := a.data.hs.1.trans_lt
    (a.radius_high_mass (c.hleft.trans_lt hiCap.1))
  have hj0 : 0 < partitionPoint 0 as j := hi0.trans_le hmass
  have herr:=physicalSampledNodeSecondMoment_increment_le n a.bf a.hf m.hbf m.hhf
    as ho he hmesh (hij.trans hj) hj hi0 hj0
  have hiSpec:=m.R_spec ⟨hiHigh,(partitionPoint_mem as ho i).2⟩
  have hjSpec:=m.R_spec ⟨hjHigh,(partitionPoint_mem as ho j).2⟩
  rw [←hiSpec,←hjSpec] at herr
  change physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) j-
    physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) i ≤
      a.radiusS (m.R (partitionPoint 0 as j))-a.radiusS (m.R (partitionPoint 0 as i))+
        2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) m.q)) at herr
  exact herr.trans (add_le_add (hinc _ hiCap _ hjCap hrad) le_rfl)

theorem sampled_increment_local_chosen
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=0) (hrightContact : P.H c.right=0 ∨ c.right=1)
    {v K : ℝ} (hv : 0 < v)
    (hleft : v ≤ a.alpha.val.val c.left+a.data.U)
    (hspan : a.alpha.val.val c.right-a.alpha.val.val c.left ≤ K*v)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ as.length)
    (hiCap : a.shiftedNativeModel.R (partitionPoint 0 as i)∈Ioo c.left c.right)
    (hjCap : a.shiftedNativeModel.R (partitionPoint 0 as j)∈Ioo c.left c.right) :
    let m:=a.shiftedNativeModel
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) j-
      physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) i ≤
        a.chosenLocalCapDiameter v K+2*(mesh*Cnode) := by
  exact c.sampled_increment_at_diameter
    (fun _ hs _ ht hst=>c.radiusS_increment_local_chosen hN hlog hnd hleftContact hrightContact
      hv hleft hspan hs ht hst) as ho he hmesh hij hj hiCap hjCap

end ShiftedCapInterval
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
