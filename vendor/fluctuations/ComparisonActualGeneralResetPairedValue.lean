module

public import ComparisonSignedCavityResetPairedValue

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def actualGeneralResetPairedProjectionValue
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    (bf hf : ℝ→ℝ≥0)
    (p : MarkedPlacement T) (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
    (partitionPoint 0 (pre++(mid++tail)) j)
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) center
  nativeStarFieldDisorderMean (restWeight n) (restFeature n) p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed P.target)) (pre.length+mid.length) 0 q
    (fun y σ=>
      (Y y (p.restSpin σ)-Y y (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.target)))*
      (nativeRestGeneratedTestValue T P R C
          (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))*
        Y y (p.restSpin σ)^d-
        nativeRestGeneratedTestValue T P R C (p.restRestrict σ)*
        Y y (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.target))^d)) 0

end OAI.SKFluctuations.Cavity
