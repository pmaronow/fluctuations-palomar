module

public import ComparisonSignedCavityTriplePairedValue
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQActualTripleIncomingSource
public import SKProof.Port.ComparisonActualOriginalQActualTripleStarIncomingSource
public import SKProof.Port.ComparisonActualOriginalQActualTriplePowerSource

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeTripleResetPairedErrorValue_original_q
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
    (partitionPoint 0 (pre++(mid++tail)) j)
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) center
  nativeStarFieldDisorderMean (restWeight n) (restFeature n) z.tree.cavityLeft
    (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed P.target)))) (pre.length+mid.length) 0 q
    (fun y σ=>
      let σold:=p.restRestrict (r.restRestrict (z.restRestrict σ))
      let old:=T.cavityLeft.atSlot σold (T.cavityLeftSlot P.target)
      let new:=z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed p.mark)))
      let F:=R (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed r.mark)))
        (z.restSpin σ)-C (z.tree.splitIndex (z.embed r.mark) z.mark)
      (Y y new-Y y old)*
        ((nativeRestGeneratedTestValue T P R C
          (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σold new)*F)*Y y new^d-
        (nativeRestGeneratedTestValue T P R C σold*F)*Y y old^d)) 0

end OAI.SKFluctuations.Cavity
