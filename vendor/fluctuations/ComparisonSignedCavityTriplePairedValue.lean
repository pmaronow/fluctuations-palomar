module

public import ComparisonSignedCavityActualTripleIncomingSource
public import ComparisonSignedCavityActualTripleStarIncomingSource
public import ComparisonSignedCavityActualTriplePowerSource
public import ComparisonSignedCavityActualResetPairedRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeTripleResetPairedErrorValue
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
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

theorem native_two_level_incoming_error_product_self (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias) (Es D : ClockTree (Spin n) tas)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Ei.Slot) (s : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) (error : D.Assignment→ℝ)
    (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelIncomingErrorProduct n j k Ei Es D H e s s qi qs center error xi xs=0 := by
  rw [native_two_level_incoming_error_product_eq_conditional]
  simp [nativeExteriorForestConditionalTest,nativeExteriorForestMean,ClockTree.expect]

theorem native_two_level_star_incoming_error_product_self (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias) (Es D : ClockTree (Spin n) tas)
    (H : Ei.Assignment→Es.Assignment→ℝ) (e : Es.Slot) (s : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) (error : D.Assignment→ℝ)
    (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelStarIncomingErrorProduct n j k Ei Es D H e s s qi qs center error xi xs=0 := by
  rw [native_two_level_star_incoming_error_product_eq_conditional]
  simp [nativeExteriorForestConditionalTest,nativeExteriorForestMean,ClockTree.expect]

theorem native_two_level_power_error_product_self (n j k : ℕ)
    {ias tas : List PositiveMass} (Ei : ClockTree (Spin n) ias) (Es D : ClockTree (Spin n) tas)
    (Z : Ei.Assignment→Es.Assignment→D.Assignment→ℝ) (s : D.Slot)
    (qi qs : ℕ→RestCoordinate n→ℝ≥0) (center : ℝ) (error : D.Assignment→ℝ)
    (xi xs : RestCoordinate n→ℝ) :
    nativeTwoLevelPowerErrorProduct n j k Ei Es D Z s s qi qs center error xi xs=0 := by
  simp [nativeTwoLevelPowerErrorProduct,nativeTwoLevelPowerProduct,
    nativeExteriorForestConditionalTest,nativeExteriorForestMean,ClockTree.expect]

end OAI.SKFluctuations.Cavity
