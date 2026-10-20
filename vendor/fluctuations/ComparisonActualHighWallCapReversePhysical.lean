module

public import ComparisonActualHighWallCapLocalPhysical

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
namespace ActualHighWallOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem sampled_reverse_local
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hleftContact : P.H c.left=0) (hrightContact : P.H c.right=0 ∨ c.right=1)
    {v K : ℝ} (hv : 0< v)
    (hleft : v≤ a.alpha.val.val c.left+comparisonSmallMass a.data.N a.data.E)
    (hspan : a.alpha.val.val c.right-a.alpha.val.val c.left≤ K*v)
    (ell : ℕ) (hell : 2< ell)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ} (hij : i≤ j) (hj : j≤ as.length)
    (hiCap : a.shiftedNativeModel.R (partitionPoint 0 as i)∈Ioo c.left c.right)
    (hjCap : a.shiftedNativeModel.R (partitionPoint 0 as j)∈Ioo c.left c.right) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    let diameter:=a.localCapDiameter v K+2*(mesh*Cnode)
    physicalSideMovementMoment (n+1) steps (m.q 0) i j≤
      diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*physicalRawRatio (n+1) ell steps 0 a.xs
          (Measure.pi fun k=>gaussianReal 0 (m.q 0 k)) id measurable_id)^(2*ell)*
            (a.xs+physicalCutMass 0 steps j)^ell)^(1/((ell:ℝ)-1)) := by
  dsimp only
  let m:=a.shiftedNativeModel
  let steps:=sampleClockSteps m.q 0 as
  have hs : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ho
  have hinc:=c.sampled_increment_local hN hlog hnd hleftContact hrightContact hv hleft hspan
    as ho he hmesh hij hj hiCap hjCap
  have hbase : 0≤ physicalPathSecondMoment (n+1) steps (m.q 0) j-
      physicalPathSecondMoment (n+1) steps (m.q 0) i:=by
    rw [←physical_movement_second_eq_profile_increment (n+1) steps hs (m.q 0) hij]
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hlR : (2:ℝ)< ell:=by exact_mod_cast hell
  have hp : 0≤((ell:ℝ)-2)/((ell:ℝ)-1):=div_nonneg (by linarith) (by linarith)
  have hpow:=Real.rpow_le_rpow hbase hinc hp
  have hraw:=physical_movement_fourth_le_raw_interpolation (n+1) ell hell steps hs (m.q 0)
    a.hxs hij (by dsimp only [steps];simp only [sampleClockSteps_length];omega)
  have hQ0 : 0≤physicalRawRatio (n+1) ell steps 0 a.xs
      (Measure.pi fun k=>gaussianReal 0 (m.q 0 k)) id measurable_id:=
    zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hmass0 : 0≤a.xs+physicalCutMass 0 steps j:=
    add_nonneg a.hxs.le (physicalCutMass_mem steps hs j).1
  have hprod : 0≤(2*physicalRawRatio (n+1) ell steps 0 a.xs
      (Measure.pi fun k=>gaussianReal 0 (m.q 0 k)) id measurable_id)^(2*ell)*
        (a.xs+physicalCutMass 0 steps j)^ell:=
    mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hQ0) _) (pow_nonneg hmass0 _)
  exact hraw.trans (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hprod _))

end ActualHighWallOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
