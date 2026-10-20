module

public import ComparisonActualGeneralTripleIncomingSource
public import ComparisonActualGeneralTripleStarIncomingSource
public import ComparisonActualGeneralTriplePowerSource
public import ComparisonSignedCavityTriplePairedValue

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Classical
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def actualGeneralTripleResetPairedErrorValue
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    (bf hf : ℝ→ℝ≥0)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
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
