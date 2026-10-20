module

public import ComparisonActualGeneralGWordPhysicalMean
public import ComparisonSignedCavityCanonicalLowFactor

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Classical
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def actualGeneralTripleSpineGValue
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    (bf hf : ℝ→ℝ≥0)
    (U : ℕ) (p : MarkedPlacement B) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  let as:=pre++(mid++tail)
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let D:=(((NativeObservedDiagram.identity B).observe p).observe r).observe z
  nativeObservedGScalar (spine.graftDiagram D) base.target U K*
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) D.tree.cavityLeft
      (D.tree.cavityLeftSlot (D.embed base.target)) (pre.length+mid.length) 0 q
      (nativeGWordProjectedPayload B base D (pre.length+mid.length) U spine.toothCount q b h K C R R) 0

theorem actual_general_triple_spine_G_value_eq
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    (bf hf : ℝ→ℝ≥0) (hbf : MonotoneOn bf (Icc 0 1)) (hhf : MonotoneOn hf (Icc 0 1))
    (ho : MassOrdered 0 (pre++(mid++tail)))
    (U : ℕ) (p : MarkedPlacement B) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)
    (hH : U ≤ z.tree.splitIndex (z.embed r.mark) z.mark) (q : ℕ→RestCoordinate n→ℝ) :
    let as:=pre++(mid++tail)
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) bf hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let D:=(((NativeObservedDiagram.identity B).observe p).observe r).observe z
    actualGeneralTripleSpineGValue spine bf hf U p r z q=
      nativeObservedGScalar (spine.graftDiagram D) base.target U K*
        (-(b (z.tree.splitIndex (z.embed r.mark) z.mark))*
          actualGeneralTripleResetPairedErrorValue n B base bf hf p r z q spine.toothCount (S (pre.length+mid.length))) := by
  dsimp only
  have HC (j) :=native_ordered_source_center_eq_completed n bf hf
    hbf hhf
    (partitionPoint_mem (pre++(mid++tail)) ho j)
  unfold actualGeneralTripleSpineGValue
  dsimp only
  rw [actual_general_G_word_triple_physical_mean pre mid tail B base p r z bf hf U spine.toothCount]
  · dsimp only
    rw [←HC]
  · intro j
    rw [HC]
  · exact hH

end OAI.SKFluctuations.Cavity
