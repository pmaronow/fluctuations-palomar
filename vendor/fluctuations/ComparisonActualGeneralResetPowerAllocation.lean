module

public import ComparisonActualGeneralCanonicalMarkedReset
public import ComparisonActualGeneralObservedDynamicExterior
public import ComparisonSignedCavityActualResetPowerSource

@[expose] public section
noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_reset_power_paired_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (ht : P.live.test.teeth=[]) (hIn : P.live.test.incoming=[])
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (hh : U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target))
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (bf hf : ℝ→ℝ≥0)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (d : ℕ) (center : ℝ) :
    let as:=pre++(mid++tail)
    let hlen : pre.length+mid.length<as.length:=
      hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
    let G:=((nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)
    let G₀:=((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered)
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    let B:=fun σ=>nativeRestGeneratedTestValue T P.live.test R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
        (p.restRestrict σ) (p.restSpin σ))
    ∃E : NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) G v q x,
    ∃t : E.D.Slot,
      (∀η ζ δ,p.restSpin (E.read η ζ δ)=E.D.atSlot δ t) ∧
      pre.length+mid.length+E.D.splitIndex E.target t=
        p.tree.splitIndex (p.embed P.live.test.target) p.mark ∧
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (pre.length+mid.length) v q
      (fun y σ=>(Y y (p.restSpin σ)-Y y
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target)))*
        (B σ*Y y (p.restSpin σ)^d-G₀.restProduct σ*Y y
          (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target))^d)) x=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>G₀.restProduct (E.read η ζ δ)) E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  have hlen : U≤(pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
  have hself : U≤T.splitIndex P.live.test.target P.live.test.target:=by rw [T.splitIndex_self];exact hlen
  obtain ⟨E⟩:=actual_general_observed_generated_dynamic_exterior_source n pre mid tail hP hmid hU
    r p hp P.live.test.target hh hself ho bf hf v q x
  have hHigh : pre.length+mid.length<p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (p.tree.cavityLeftSlot p.mark) := by
    rw [cavityLeft_splitIndex,splitIndex_symm]
    exact hU.trans_le hh
  obtain ⟨t,htRead,htSplit⟩:=E.high (p.tree.cavityLeftSlot p.mark) hHigh
  refine ⟨E,t,htRead,?_,?_⟩
  · simpa only [cavityLeft_splitIndex] using htSplit
  · have hB (σ : p.tree.cavityLeft.Assignment) :
        nativeRestGeneratedTestValue T P.live.test
          (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
          (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
            (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
            (partitionPoint 0 (pre++(mid++tail)) j))
          (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
            (p.restRestrict σ) (p.restSpin σ))=
        (((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)).retainOnMarked r p hp).canonicalPhysicalSource bf hf
          (fun _=>NativeSourceFactorForm.centered)).restProduct σ := by
      rw [actual_general_generated_marked_canonical_rest_product]
      apply sub_eq_zero.mp
      have H:=native_rest_generated_reset_replace_sub P.live.test P.live.ancestry ht
        (by omega) (hU.trans_le hlen)
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
          (partitionPoint 0 (pre++(mid++tail)) j)) (p.restRestrict σ) (p.restSpin σ)
      simpa only [hIn,List.map_nil,List.sum_nil,mul_zero] using H
    have H:=E.paired_no_incoming_allocation ho (p.tree.cavityLeftSlot p.mark) t htRead
      (((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)).retainOnMarked r p hp).canonicalPhysicalSource bf hf
        (fun _=>NativeSourceFactorForm.centered)).restProduct d center
    simp_rw [hB]
    simpa only [p.restRestrict_at,MarkedPlacement.restSpin] using H

end OAI.SKFluctuations.Cavity
