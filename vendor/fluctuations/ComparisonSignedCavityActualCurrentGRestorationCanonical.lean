module

public import ComparisonSignedCavityCurrentGOriginalLawRestoration
public import ComparisonSignedCavityGeneratedCompleteShape

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

 theorem native_actual_current_G_restoration_eq_canonical_source
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (q : ℕ→RestCoordinate n→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let G:=nativeGeneratedCompleteShape n P.live.test P.live.ancestry hi
      (hs.trans_le hP.highCut_le_length)
    nativeActualGProjectedRestoration T P.live.test star U M q=
      nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q b h K S
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct := by
  dsimp only
  let G:=nativeGeneratedCompleteShape n P.live.test P.live.ancestry hi
    (hs.trans_le hP.highCut_le_length)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  have HP : (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct=
      nativeRestGeneratedTestValue T P.live.test R C :=
    funext (native_generated_complete_canonical_rest_product n P.live.test P.live.ancestry hi
      (hs.trans_le hP.highCut_le_length) M)
  rw [HP]
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HC (j : ℕ) : orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)=C j:=
    native_ordered_source_center_eq_completed n M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have HCfun : C=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j):=funext (fun j=>(HC j).symm)
  unfold nativeActualGProjectedRestoration
  dsimp only
  change nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q _ _ _ C R
      (nativeRestGeneratedTestValue T P.live.test R C)=_
  rw [HCfun]

end OAI.SKFluctuations.Cavity
