module

public import ComparisonNativeCavityGoodStarTransfer
public import ComparisonNativeStarOriginalBufferTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000

theorem nativeRetainedCenteredMoment_eq_physicalStar
    (n l : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u S : ℝ) :
    nativeRetainedCenteredMoment n l b h as u S=
      physicalStarPairMoment (n+1) l
        (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (Measure.pi fun i=>gaussianReal 0 (completedPathClock (n+1) b h 0 i))
        id measurable_id
        (physicalRetainedIndex (sampleClockSteps (completedPathClock (n+1) b h) 0 as) u).val S := by
  let Q := physicalCompletedClock (n+1)
    (fun j=>(b (partitionPoint 0 as j):ℝ)) (fun j=>(h (partitionPoint 0 as j):ℝ))
  have H := physicalStarPairMoment_eq_pairDisorder (n+1) l as ho Q
    (retainedMassPrefixIndex u as) (retainedMassPrefixIndex_le_length u as) S
  have hroot : Q 0=(fun i=>(completedPathClock (n+1) b h 0 i:ℝ)) := by
    have hq := congrFun (actual_sampled_completed_clock_eq (n+1) b h hb hh as ho) 0
    simpa only [stepClockValues_zero,Q] using hq.symm
  have hsteps := actual_sampled_completed_diagonal_steps_eq (n+1) b h hb hh as ho
  rw [hsteps,hroot] at H
  simpa only [nativeRetainedCenteredMoment,nativeRetainedPairValue,
    physicalRetainedIndex,retainedMass_splitClockSteps_length,
    retainedMassPrefixIndex,Real.toNNReal_coe,Q] using H.symm

end OAI.SKFluctuations.LaplaceWindowFormalization
