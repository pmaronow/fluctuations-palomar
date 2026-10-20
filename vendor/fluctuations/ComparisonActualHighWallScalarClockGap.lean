module

public import ComparisonSignedCavityScalarMinimumBuffer
public import ComparisonActualHighWallContinuumClockMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

 theorem high_field_strictMonoOn
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    StrictMonoOn M.hf (Icc M.data.s 1) := by
  intro u hu v hv huv
  have HR : M.data.wallRadius M.alpha u < M.data.wallRadius M.alpha v:=by
    by_contra H
    have HE:=le_antisymm (le_of_not_gt H) (M.data.wallRadius_monotone M.alpha huv.le)
    have HX:=congrArg M.alpha.val.val HE
    rw [M.data.wallRadius_spec M.alpha hv,M.data.wallRadius_spec M.alpha hu] at HX
    exact (ne_of_lt huv) HX.symm
  have HRu:=M.data.wallRadius_bounds M.alpha u
  have HRv:=M.data.wallRadius_bounds M.alpha v
  have H:=laplaceComparisonField_strictMonoOn M.data.hd.ne' (sq_pos_of_pos M.data.hd)
    ⟨M.data.hrbounds.1.le.trans HRu.1,HRu.2⟩
    ⟨M.data.hrbounds.1.le.trans HRv.1,HRv.2⟩ HR
  apply NNReal.coe_lt_coe.mp
  rw [M.data.high_field_clock M.alpha hu,M.data.high_field_clock M.alpha hv]
  exact H

 theorem scalar_buffer_original_clock_gap_above_wall
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U V : ℕ)
    (hhigh : M.data.s ≤ partitionPoint 0 as U)
    (hmass : partitionPoint 0 as U < partitionPoint 0 as V) :
    nativeContinuumMixedClock n M.bf M.hf as U < nativeContinuumMixedClock n M.bf M.hf as V := by
  have hUV : U ≤ V:=by
    by_contra H
    exact (not_le_of_gt hmass) (partitionPoint_mono as ho (le_of_not_ge H))
  have hu:=partitionPoint_mem as ho U
  have hv:=partitionPoint_mem as ho V
  have huv:=partitionPoint_mono as ho hUV
  have HB:=NNReal.coe_le_coe.mpr (M.data.bf_monotone M.alpha hu hv huv)
  have HH:=NNReal.coe_lt_coe.mpr (M.high_field_strictMonoOn
    ⟨hhigh,hu.2⟩ ⟨hhigh.trans huv,hv.2⟩ hmass)
  have HS:=physicalOrderedPathS_monotone_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu hv huv
  have HS0:=(physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu).1
  have Hprod:=mul_le_mul HB HS HS0 (NNReal.coe_nonneg _)
  unfold nativeContinuumMixedClock
  nlinarith only [HH,Hprod]

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallOverlapMinimum
