module

public import ComparisonSignedCavityActualResetStarIncomingSource
public import ComparisonSignedCavityActualResetIncomingSource
public import ComparisonSignedCavityActualPairedStarIncomingRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeResetPairedProjectionValue
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
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

theorem native_two_level_incoming_product_self (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias) (Es D : ClockTree (Spin n) tas)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Ei.Slot) (s : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelIncomingProduct n j k Ei Es D H e s s qi qs center xi xs=0 := by
  simp [nativeTwoLevelIncomingProduct,ClockTree.expect]

theorem native_two_level_star_incoming_product_self (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias) (Es D : ClockTree (Spin n) tas)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Es.Slot) (s : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelStarIncomingProduct n j k Ei Es D H e s s qi qs center xi xs=0 := by
  simp [nativeTwoLevelStarIncomingProduct,ClockTree.expect]

theorem native_two_level_power_product_self (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias) (Es D : ClockTree (Spin n) tas)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (s : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelPowerProduct n j k Ei Es D Z s s qi qs center xi xs=0 := by
  simp [nativeTwoLevelPowerProduct,nativeExteriorForestConditionalTest,
    nativeExteriorForestMean,ClockTree.expect]

end OAI.SKFluctuations.Cavity
