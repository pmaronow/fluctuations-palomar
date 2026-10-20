module

public import ComparisonActualHighWallBufferEndpointGeometry
public import ComparisonSignedCavityActualSlowWindowSequence

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer NativeOverlapMinimum
namespace ActualHighWallOverlapMinimum

def IsActualHighWallCalibratedSlowWindow
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W L Cs : ℝ) (w : ActualSlowWindowChoice) : Prop :=
  let a := calibratedBandStart cu Az
  let b := a+4*L
  let c := starMassBandConstant cu Az/cu
  let c1 := actualSlowWindowExponent m delta
  let S := orderedPathS (n+1) M.bf M.hf
  ∃p : M.Potential,
    w.index < w.blocks ∧ 0 < w.blocks ∧ 0 < w.quarter ∧
    M.data.N^(-c1)*W ≤ w.quarter ∧ 4*(w.blocks:ℝ)*w.quarter=4*L*W ∧
    (∀j ≤ 4*w.blocks,massNode (a*W) w.quarter j ∈ Icc (a*W) (b*W)) ∧
    w.star.val ∈ Ioo (massNode (a*W) w.quarter (4*w.index+1)+w.quarter/2)
      (massNode (a*W) w.quarter (4*w.index+3)-w.quarter/2) ∧
    p.H (M.data.wallRadius M.alpha w.star.val) ≤ 0 ∧
    orderedPathB (n+1) M.bf M.hf w.star.val-(S w.star.val)^2 ≤
      M.data.N^(-(actualMassSavingExponent m delta/4))*W^2 ∧
    (3*c/4)*W ≤ S w.star.val ∧ S w.star.val ≤ Cs*W ∧
    (a/cu)*W ≤ M.data.wallRadius M.alpha w.star.val ∧ M.data.wallRadius M.alpha w.star.val ≤ (b/cl)*W ∧
    M.xs ≤ M.data.wallRadius M.alpha w.star.val ∧ M.z ≤ M.data.wallRadius M.alpha w.star.val/2 ∧
    (3*M.data.T*c/8)*W ≤ actualMixedClock (n+1) M.bf M.hf w.star.val ∧
    |actualMixedClock (n+1) M.bf M.hf w.star.val-M.data.T*S w.star.val| ≤ ((c+1)/4)*W^3 ∧
    (∀v∈Icc (massNode (a*W) w.quarter (4*w.index))
      (massNode (a*W) w.quarter (4*(w.index+1))),
      |S v-S w.star.val| ≤ M.data.N^(-c1/2)*W)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
