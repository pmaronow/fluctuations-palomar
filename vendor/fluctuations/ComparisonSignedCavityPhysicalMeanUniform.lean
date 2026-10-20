module

public import ComparisonSignedCavitySampledMeanUniform
public import PhysicalSampledNodeOverlapError

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem sampled_finite_physical_mean_eq_sampled (n : ℕ)
    (bf hf : ℝ → ℝ≥0) (hb : MonotoneOn bf (Icc (0:ℝ) 1))
    (hh : MonotoneOn hf (Icc (0:ℝ) 1)) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (j : ℕ) (hj : j ≤ as.length) :
    finitePhysicalMean (n+1) as (fun k => (bf (partitionPoint 0 as k):ℝ))
      (fun k => (hf (partitionPoint 0 as k):ℝ)) j =
      physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) bf hf) 0 as)
        (completedPathClock (n+1) bf hf 0) j := by
  have hzero : (fun i => Real.toNNReal (physicalCompletedClock (n+1)
      (fun k => (bf (partitionPoint 0 as k):ℝ))
      (fun k => (hf (partitionPoint 0 as k):ℝ)) 0 i))=completedPathClock (n+1) bf hf 0 := by
    funext i
    cases i <;> simp [physicalCompletedClock,completedPathClock,partitionPoint]
  unfold finitePhysicalMean
  rw [Nat.min_eq_left hj]
  dsimp only
  rw [actual_sampled_completed_diagonal_steps_eq (n+1) bf hf hb hh as ho,hzero]

theorem finite_physical_mean_uniform_continuum_error (n : ℕ)
    (bf hf : ℝ → ℝ≥0) (hb : MonotoneOn bf (Icc (0:ℝ) 1))
    (hh : MonotoneOn hf (Icc (0:ℝ) 1)) (hroot : hf 0=0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh : PartitionMesh mesh 0 as)
    (j : ℕ) (hj : j ≤ as.length) :
    |finitePhysicalMean (n+1) as (fun k => (bf (partitionPoint 0 as k):ℝ))
        (fun k => (hf (partitionPoint 0 as k):ℝ)) j-
      nativePhysicalResourceCenter n bf hf as j| ≤
        mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n+1) bf hf)) := by
  let q := completedPathClock (n+1) bf hf
  let V := clockVariationBound (physicalFeatureCoordinateBound n) q
  have hV : 0 ≤ V := clockVariationBound_nonneg _ q (completedPathClock_monotone (n+1) hb hh)
  by_cases hpos : 0 < partitionPoint 0 as j
  · have H := physicalSampledNodeSecondMoment_error n bf hf hb hh as ho he hmesh j hj hpos
    rw [sampled_finite_physical_mean_eq_sampled n bf hf hb hh as ho j hj,
      native_physical_resource_center_at_positive_cut n bf hf hb hh as ho j hpos]
    exact H
  · have hj0 : j=0 := by
      cases as with
      | nil => simpa using hj
      | cons b bs =>
        cases j with
        | zero => rfl
        | succ j =>
          have H := (partitionPoint_mem bs ho.2.2 j).1
          exact False.elim (hpos (b.property.trans_le H))
    subst j
    rw [finitePhysicalMean_zero_of_bare_root (n+1) ho _ _
      (by simp [partitionPoint,hroot])]
    have hzeroPoint : partitionPoint 0 as 0=0 := by cases as <;> rfl
    simp only [nativePhysicalResourceCenter,hzeroPoint,pathPairMoment,
      lt_self_iff_false,dite_false,sub_self,abs_zero]
    change 0 ≤ mesh*(2*ClockTree.errorJetVariation 2 0 0*V)
    exact mul_nonneg hmesh0 (mul_nonneg (mul_nonneg (by norm_num)
      (ClockTree.errorJetVariation_nonneg 2 0 0)) hV)

end OAI.SKFluctuations.Cavity
