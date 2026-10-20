module

public import ComparisonActualHighOnlyContactGeometry
public import ComparisonSignedCavityInnovationClock
public import ComparisonSignedCavityActualBoundarySchedule

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem radius_high_mass {u : ℝ} (hu : 0 < a.R u) : a.data.s < u := by
  have HL:=omittedSweepQuantile_left zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
    a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha
  by_contra H
  have HM:=omittedSweepQuantile_monotone zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
    a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha (le_of_not_gt H)
  change a.R u ≤ a.R a.data.s at HM
  change a.R a.data.s=0 at HL
  rw [HL] at HM
  exact hu.not_ge HM

theorem high_field_radius_gap
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {u v : ℝ} (hu : u∈Icc a.data.s 1) (hv : v∈Icc a.data.s 1) (huv : u ≤ v) :
    ((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam (a.R v)*
      (a.R v-a.R u) ≤ (a.hf v:ℝ)-(a.hf u:ℝ) := by
  rw [(a.high_clock_coe hv).2,(a.high_clock_coe hu).2]
  have HB:=a.data.hh ⟨a.data.hs.1.trans hu.1,hu.2⟩ ⟨a.data.hs.1.trans hv.1,hv.2⟩ huv
  have HRu:=omittedSweepQuantile_bounds zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
    a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha u
  have HRv:=omittedSweepQuantile_bounds zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
    a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha v
  have HR:=omittedSweepQuantile_monotone zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
    a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha huv
  have HG:=actual_comparison_radius_field_increment_lower hN hlog a.data.hd hnd
    a.hlam a.hld HRu.1 HRv.2 HR
  linarith only [HB,HG]

theorem sampled_radius_step_le (as : List PositiveMass)
    (ho : MassOrdered 0 as) {mesh : ℝ} (hmesh : 0 ≤ mesh)
    (hpart : PartitionMesh mesh 0 as) (j : ℕ) :
    a.R (partitionPoint 0 as (j+1))-
      a.R (partitionPoint 0 as j) ≤ mesh/(a.data.k 1) := by
  have h:=(omittedSweepQuantile_lipschitz zero_le_one ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha).dist_le_mul
    (partitionPoint 0 as (j+1)) (partitionPoint 0 as j)
  have hp:=partitionPoint_mono as ho (Nat.le_succ j)
  have hR:=omittedSweepQuantile_monotone zero_le_one ⟨a.data.hs.1,a.data.hs1⟩ a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha hp
  change abs (a.R (partitionPoint 0 as (j+1))-
    a.R (partitionPoint 0 as j)) ≤ (1/(a.data.k 1))*
      abs (partitionPoint 0 as (j+1)-partitionPoint 0 as j) at h
  rw [abs_of_nonneg (sub_nonneg.mpr hR),abs_of_nonneg (sub_nonneg.mpr hp)] at h
  apply h.trans
  have hm:=partitionPoint_step_le_mesh as hpart hmesh j
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr a.data.hc.le)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
