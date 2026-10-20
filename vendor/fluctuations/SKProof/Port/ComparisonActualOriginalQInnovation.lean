module

public import SKProof.Port.ComparisonActualOriginalQContactGeometry
public import ComparisonActualHighWallThetaZeroHighFieldGap
public import ComparisonSignedCavityInnovationClock
public import ComparisonSignedCavityActualBoundarySchedule

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem sampled_radius_step_le (as : List PositiveMass)
    (ho : MassOrdered 0 as) {mesh : ℝ} (hmesh : 0 ≤ mesh)
    (hpart : PartitionMesh mesh 0 as) (j : ℕ) :
    a.sweepRadius (partitionPoint 0 as (j+1))-
      a.sweepRadius (partitionPoint 0 as j) ≤ mesh/(a.data.k 1) := by
  have h:=(a.sweepRadius_lipschitz).dist_le_mul
    (partitionPoint 0 as (j+1)) (partitionPoint 0 as j)
  have hp:=partitionPoint_mono as ho (Nat.le_succ j)
  have hR:=a.sweepRadius_monotone hp
  change abs (a.sweepRadius (partitionPoint 0 as (j+1))-
    a.sweepRadius (partitionPoint 0 as j)) ≤ (1/(a.data.k 1))*
      abs (partitionPoint 0 as (j+1)-partitionPoint 0 as j) at h
  rw [abs_of_nonneg (sub_nonneg.mpr hR),abs_of_nonneg (sub_nonneg.mpr hp)] at h
  apply h.trans
  have hm:=partitionPoint_step_le_mesh as hpart hmesh j
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr a.data.hc.le)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
