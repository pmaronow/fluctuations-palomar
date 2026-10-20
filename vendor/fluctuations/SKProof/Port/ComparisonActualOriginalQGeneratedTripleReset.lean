module

public import ComparisonSignedCavityGeneratedTripleReset
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQActualTripleHighDynamicSource

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_triple_canonical_rest_product_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (hi : i ≤ star) (hlen : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (σ : z.tree.cavityLeft.Assignment) :
    (((((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j))
        (p.restRestrict (r.restRestrict (z.restRestrict σ))) := by
  exact actual_general_generated_triple_canonical_rest_product n P hP hi hlen M.sweepBf M.sweepHf p hp r hr z hz σ

theorem native_generated_triple_reset_change_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (ht : P.teeth=[])
    (hi : i ≤ star) (hlen : star < as.length) (e₀ : T.Slot) (hIncoming : P.incoming=[e₀])
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (σ : z.tree.cavityLeft.Assignment) :
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    nativeRestGeneratedTestValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target)
        (p.restRestrict (r.restRestrict (z.restRestrict σ)))
        (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed p.mark)))))-
      (((((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      (((((nativeGeneratedExteriorShape n P hP hi hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct σ*
      (R (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed p.mark))))
          (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed e₀)))))-
        R (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed P.target)))))
          (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed e₀)))))) := by
  exact actual_general_generated_triple_reset_change n P hP ht hi hlen e₀ hIncoming M.sweepBf M.sweepHf p hp r hr z hz σ

end OAI.SKFluctuations.Cavity
