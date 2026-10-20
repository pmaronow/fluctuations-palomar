module

public import ComparisonNativeActualCutLowErrorDensityProducer
public import ComparisonSignedCavityActualNaturalBoundaryBudget
public import PhysicalSampledNodeOverlapError

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def nativeOriginalCutLowErrorSecond (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (j : ℕ) : ℝ :=
  rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) b h 0)
    (fun σ τ=>(orderedOverlap (n+1) σ τ-orderedPathS (n+1) b h (partitionPoint 0 as j))^2)
    (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j

def nativeOriginalCutLowErrorRadius (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (j : ℕ) : ℝ :=
  Real.sqrt (nativeOriginalCutLowErrorSecond n b h as j)

theorem nativeOriginalCutLowErrorSecond_nonneg (n : ℕ) (b h : ℝ→ℝ≥0)
    {as : List PositiveMass} (ha : MassOrdered 0 as) (j : ℕ) :
    0 ≤ nativeOriginalCutLowErrorSecond n b h as j := by
  unfold nativeOriginalCutLowErrorSecond
  have H:=rootLevelPairMean_mono (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) b h 0) (fun σ τ=>sq_nonneg
      (orderedOverlap (n+1) σ τ-orderedPathS (n+1) b h (partitionPoint 0 as j)))
    (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
    (sampleClockSteps_ordered _ _ ha) j
  rw [rootLevelPairMean_const (uniformWeight_pos _) _ _ _ (sampleClockSteps_ordered _ _ ha)] at H
  exact H

theorem nativeOriginalCutLowErrorSecond_eq_pairDisorder (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {as : List PositiveMass} (ha : MassOrdered 0 as) (j : ℕ) :
    nativeOriginalCutLowErrorSecond n b h as j=
      (ClockTree.pairClock as j).disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1)) 0
        (Cavity.physicalCompletedClock (n+1)
          (fun k=>(b (partitionPoint 0 as k):ℝ)) (fun k=>(h (partitionPoint 0 as k):ℝ)))
        (fun σ=>(orderedOverlap (n+1) (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2-
          orderedPathS (n+1) b h (partitionPoint 0 as j))^2) 0 := by
  let Q:=fun σ τ : Spin (n+1)=>
    (orderedOverlap (n+1) σ τ-orderedPathS (n+1) b h (partitionPoint 0 as j))^2
  change nativeOriginalCutLowErrorSecond n b h as j=
    (ClockTree.pairClock as j).disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1)) (fun _=>0)
      (Cavity.physicalCompletedClock (n+1) (fun k=>(b (partitionPoint 0 as k):ℝ))
        (fun k=>(h (partitionPoint 0 as k):ℝ)))
      (fun σ=>Q (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) 0
  rw [ClockTree.pairDisorder_eq_rootLevelPairMean (uniformWeight_pos _) _ _ ha _ j Q]
  rw [Cavity.actual_sampled_completed_diagonal_steps_eq (n+1) b h hb hh as ha]
  unfold nativeOriginalCutLowErrorSecond
  congr 1
  funext i
  cases i <;> simp only [Cavity.physicalCompletedClock,completedPathClock,partitionPoint,
    partitionValues_zero,Sum.elim_inl,Sum.elim_inr,Real.toNNReal_coe,id_eq]

theorem physicalSampledCutLowErrorSecond_eq_massStepFunction (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    physicalSampledCutLowErrorSecond n b h as ha u=
      massStepFunction as (nativeOriginalCutLowErrorSecond n b h as) u := by
  let steps:=sampleClockSteps (completedPathClock (n+1) b h) 0 as
  have ho : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ha
  have hmass : positiveStepMasses steps ho.mem_pos=as := sampleClockSteps_masses _ _ _ ho.mem_pos
  have hcenter : partitionSample (orderedPathS (n+1) b h) 0 as u=
      orderedPathS (n+1) b h (partitionPoint 0 as (splitClockSteps u steps).1.length) := by
    unfold partitionSample
    rw [←hmass,massStepFunction_split_index]
    exact partitionValues_point _ _ _ _
  unfold physicalSampledCutLowErrorSecond
  rw [physical_sampled_pair_eq_root_level n b h as ha,hcenter]
  have HM:=massStepFunction_split_index u steps ho.mem_pos (nativeOriginalCutLowErrorSecond n b h as)
  rw [hmass] at HM
  rw [HM]
  rfl

theorem massStepFunction_comp_real (as : List PositiveMass) (f : ℕ→ℝ) (g : ℝ→ℝ) (u : ℝ) :
    massStepFunction as (fun j=>g (f j)) u=g (massStepFunction as f u) := by
  induction as generalizing f with
  | nil => rfl
  | cons b bs ih => simp only [massStepFunction]; split_ifs <;> first | rfl | exact ih _

theorem physicalSampledCutLowErrorRadius_eq_massStepFunction (n : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    Real.sqrt (physicalSampledCutLowErrorSecond n b h as ha u)=
      massStepFunction as (nativeOriginalCutLowErrorRadius n b h as) u := by
  rw [physicalSampledCutLowErrorSecond_eq_massStepFunction]
  exact (massStepFunction_comp_real as _ Real.sqrt u).symm

theorem native_low_edgeBudget_eq_prefix_cells (as : List PositiveMass) (a : ℝ)
    (U : ℕ) (hU : U ≤ as.length) (f : ℕ→ℝ) :
    ClockTree.edgeBudget a as (fun j=>if j<U then f j else 0)=massCellSum (as.take U) a f := by
  induction U generalizing as a f with
  | zero =>
    have hz : ClockTree.edgeBudget a as (fun _=>0)=0 := by
      induction as generalizing a with
      | nil => simp [ClockTree.edgeBudget]
      | cons b bs ih => simp [ClockTree.edgeBudget,ih]
    simpa only [Nat.not_lt_zero,ite_false,List.take_zero,massCellSum] using hz
  | succ U ih =>
    cases as with
    | nil => simp only [List.length_nil] at hU; omega
    | cons b bs =>
      simp only [ClockTree.edgeBudget,List.take_succ_cons,massCellSum,
        Nat.zero_lt_succ,ite_true]
      have hf : (fun j=>if 1+j<U+1 then f (1+j) else 0)=
          (fun j=>if j<U then f (j+1) else 0) := by
        funext j
        simp only [Nat.add_comm,Nat.add_lt_add_iff_right]
      rw [hf,ih bs b.val (by simp only [List.length_cons] at hU; omega)]

theorem native_low_edgeBudget_eq_prefix_integral {as : List PositiveMass}
    (ha : MassOrdered 0 as) (U : ℕ) (hU : U ≤ as.length) (f : ℕ→ℝ) :
    ClockTree.edgeBudget 0 as (fun j=>if j<U then f j else 0)=
      (∫u in 0..partitionPoint 0 as U,massStepFunction as f u) := by
  rw [native_low_edgeBudget_eq_prefix_cells as 0 U hU]
  have HH:=massStepFunction_internal_band_integral [] (as.take U) (as.drop U)
    (show MassOrdered 0 [] by exact ⟨le_rfl,zero_le_one⟩) rfl
    (massPartition_take_ordered as ha U) (massPartition_take_end 0 as U)
    (massPartition_drop_ordered as ha U) f
  simpa only [List.nil_append,List.take_append_drop,List.length_nil,zero_add,partitionEnd] using HH.symm

namespace NativeOverlapMinimum

theorem actual_cut_low_error_edgeBudget_on_every_final_net
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 0 < C) (us : List PositiveMass) (hu : ∀u∈us,u.val ≤ 1) :
    ∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ min (C*a.canonicalDirectTestBandScale) 1 →
        ClockTree.edgeBudget 0 as (fun k=>if k<U then nativeOriginalCutLowErrorRadius n a.bf a.hf as k else 0) ≤
          a.actualOriginalLowErrorDensitySaving C*a.xs^2 := by
  filter_upwards [a.actual_cut_low_error_density_on_every_final_net C hC us hu] with j hj
  dsimp only
  intro U hU hmass
  let as:=finiteCutMasses us j
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hu j
  rw [native_low_edgeBudget_eq_prefix_integral ho U hU]
  have heq : massStepFunction as (nativeOriginalCutLowErrorRadius n a.bf a.hf as)=
      fun u=>Real.sqrt (physicalSampledCutLowErrorSecond n a.bf a.hf as ho u) := by
    funext u
    exact (physicalSampledCutLowErrorRadius_eq_massStepFunction n a.bf a.hf as ho u).symm
  rw [heq]
  have hi:=native_intervalIntegrable_sqrt_of_intervalIntegrable
    (physicalSampledCutLowErrorSecond_intervalIntegrable n a.bf a.hf
      (toNNReal_monotoneOn (comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk a.context.hkc
        a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha).1)
      (toNNReal_monotoneOn (comparisonVariableEndpoint_clocks_admissible a.context.hc a.context.hk a.context.hkc
        a.context.hm a.context.hM a.b a.h a.context.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha).2.1)
      as ho (finiteCutMasses_mesh us hu j))
  have hq : min (C*a.canonicalDirectTestBandScale) 1∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_pos hC a.canonical_direct_test_band_pos).le zero_le_one,min_le_right _ _⟩
  have hiq:=hi.mono_set (by
    rw [uIcc_of_le hq.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2)
  apply (intervalIntegral.integral_mono_interval le_rfl (partitionPoint_mem as ho U).1 hmass
    (ae_of_all _ (fun u=>Real.sqrt_nonneg (physicalSampledCutLowErrorSecond n a.bf a.hf as ho u))) hiq).trans
  exact hj

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
