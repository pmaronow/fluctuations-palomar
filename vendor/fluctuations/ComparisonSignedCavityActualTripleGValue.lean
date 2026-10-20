module

public import ComparisonSignedCavityGWordPhysicalMean
public import ComparisonSignedCavityCanonicalLowFactor

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
open Set
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualTripleSpineGValue
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (U : ℕ) (p : MarkedPlacement B) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  let as:=pre++(mid++tail)
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let D:=(((NativeObservedDiagram.identity B).observe p).observe r).observe z
  nativeObservedGScalar (spine.graftDiagram D) base.target U K*
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) D.tree.cavityLeft
      (D.tree.cavityLeftSlot (D.embed base.target)) (pre.length+mid.length) 0 q
      (nativeGWordProjectedPayload B base D (pre.length+mid.length) U spine.toothCount q b h K C R R) 0

theorem native_actual_triple_spine_G_value_eq
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail)))
    (U : ℕ) (p : MarkedPlacement B) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    (hH : U ≤ z.tree.splitIndex (z.embed r.mark) z.mark) (q : ℕ→RestCoordinate n→ℝ) :
    let as:=pre++(mid++tail)
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let D:=(((NativeObservedDiagram.identity B).observe p).observe r).observe z
    nativeActualTripleSpineGValue spine M U p r z q=
      nativeObservedGScalar (spine.graftDiagram D) base.target U K*
        (-(b (z.tree.splitIndex (z.embed r.mark) z.mark))*
          nativeTripleResetPairedErrorValue n B base M p r z q spine.toothCount (S (pre.length+mid.length))) := by
  dsimp only
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HC (j) :=native_ordered_source_center_eq_completed n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    (partitionPoint_mem (pre++(mid++tail)) ho j)
  unfold nativeActualTripleSpineGValue
  dsimp only
  rw [native_G_word_triple_physical_mean pre mid tail B base p r z M U spine.toothCount]
  · dsimp only
    rw [←HC]
  · intro j
    rw [HC]
  · exact hH

end OAI.SKFluctuations.Cavity
