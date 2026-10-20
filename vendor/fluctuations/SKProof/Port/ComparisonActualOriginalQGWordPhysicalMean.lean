module

public import ComparisonSignedCavityGWordPhysicalMean
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQTriplePairedValue

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open scoped NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_G_word_triple_physical_mean_original_q
    {n : ℕ} (pre mid tail : List PositiveMass)
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (base : NativeGeneratedTest T)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (U power : ℕ) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*
      pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
        (partitionPoint 0 (pre++(mid++tail)) j))
    (hH : U ≤ z.tree.splitIndex (z.embed r.mark) z.mark) :
    let D:=(((NativeObservedDiagram.identity T).observe p).observe r).observe z
    let star:=pre.length+mid.length
    let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
      (partitionPoint 0 (pre++(mid++tail)) j)
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) D.tree.cavityLeft
      (D.tree.cavityLeftSlot (D.embed base.target)) star 0 q
      (nativeGWordProjectedPayload T base D star U power q b h K C R R) 0=
      -(b (z.tree.splitIndex (z.embed r.mark) z.mark))*
        nativeTripleResetPairedErrorValue_original_q n T base M p r z q power (C star) := by
  dsimp only
  let D:=(((NativeObservedDiagram.identity T).observe p).observe r).observe z
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
    (partitionPoint 0 (pre++(mid++tail)) j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  have HRead (σ : z.tree.cavityLeft.Assignment) :
      D.restRead σ=p.restRestrict (r.restRestrict (z.restRestrict σ)) := by
    change ((((NativeObservedDiagram.identity T).observe p).observe r).observe z).restRead σ=_
    rw [NativeObservedDiagram.restRead_observe,NativeObservedDiagram.restRead_observe,
      NativeObservedDiagram.restRead_observe,NativeObservedDiagram.restRead_identity]
  have HP:=fun y σ=>native_G_word_physical_projected_payload pre mid tail T base D
    z.mark (z.embed r.mark) (z.embed (r.embed p.mark)) rfl U power q b h K C hKC hH y σ
  change nativeStarFieldDisorderMean (restWeight n) (restFeature n) D.tree.cavityLeft
    (D.tree.cavityLeftSlot (D.embed base.target)) (pre.length+mid.length) 0 q
    (nativeGWordProjectedPayload T base D (pre.length+mid.length) U power q b h K C R R) 0=_
  have HF:=funext (fun y=>funext (fun σ=>HP y σ))
  rw [HF,native_star_field_disorder_mean_const_mul]
  congr 1
  unfold nativeTripleResetPairedErrorValue_original_q nativeStarSuffixClock
  simp_rw [HRead]
  rfl

end OAI.SKFluctuations.Cavity
