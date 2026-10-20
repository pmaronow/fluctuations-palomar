module

public import ComparisonSignedCavityGeneratedTripleReset
public import ComparisonSignedCavityPairedErrorAllocation

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_triple_reset_power_error_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (ht : P.live.test.teeth=[]) (hIn : P.live.test.incoming=[])
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark)
    (hrH : U ≤ r.tree.splitIndex (r.embed (p.embed P.live.test.target)) r.mark)
    (hzH : U ≤ z.tree.splitIndex (z.embed (r.embed (p.embed P.live.test.target))) z.mark)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (d : ℕ) (center : ℝ) :
    let as:=pre++(mid++tail)
    let hlen : pre.length+mid.length < as.length:=
      hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))
    let G:=((((nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
    let G₀:=((((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    let s:=z.tree.cavityLeftSlot (z.embed (r.embed (p.embed P.live.test.target)))
    let c₀:=z.tree.cavityLeftSlot (z.embed (r.embed p.mark))
    let e₁:=z.tree.cavityLeftSlot (z.embed r.mark)
    let e₂:=z.tree.cavityLeftSlot z.mark
    let B:=fun σ=>nativeRestGeneratedTestValue T P.live.test R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
        (p.restRestrict (r.restRestrict (z.restRestrict σ))) (z.tree.cavityLeft.atSlot σ c₀))
    let F:=fun σ=>R (z.tree.cavityLeft.atSlot σ e₁) (z.tree.cavityLeft.atSlot σ e₂)-
      C (z.tree.splitIndex (z.embed r.mark) z.mark)
    ∃E : NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail z.tree s G v q x,
    ∃(c e f : E.D.Slot),
      (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ) c₀=E.D.atSlot δ c) ∧
      (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ) e₁=E.D.atSlot δ e) ∧
      (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ) e₂=E.D.atSlot δ f) ∧
      pre.length+mid.length+E.D.splitIndex E.target c=
        z.tree.splitIndex (z.embed (r.embed (p.embed P.live.test.target))) (z.embed (r.embed p.mark)) ∧
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    let error:=fun δ=>R (E.D.atSlot δ e) (E.D.atSlot δ f)-C (z.tree.splitIndex (z.embed r.mark) z.mark)
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) z.tree.cavityLeft s
      (pre.length+mid.length) v q
      (fun y σ=>(Y y (z.tree.cavityLeft.atSlot σ c₀)-Y y (z.tree.cavityLeft.atSlot σ s))*
        ((B σ*F σ)*Y y (z.tree.cavityLeft.atSlot σ c₀)^d-
          (G₀.restProduct σ*F σ)*Y y (z.tree.cavityLeft.atSlot σ s)^d)) x=
      ∑j∈Finset.range d,∫w,nativeTwoLevelPowerErrorProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>G₀.restProduct (E.read η ζ δ)) E.target c qi qs center error
        (exteriorForestIRoot w) (exteriorForestStarRoot w)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  have hlen : U ≤ (pre++(mid++tail)).length:=hpH.trans (p.tree.splitIndex_le_clockLength _ _)
  obtain ⟨E,c,e,f,hc,he,hf,hcs,_hes,_hfs⟩:=
    native_actual_generated_triple_high_dynamic_exterior_source n pre mid tail hP hmid hU
      p hp r hr z hz hpH hrH hzH ho M v q x
  refine ⟨E,c,e,f,hc,he,hf,hcs,?_⟩
  have HB (σ : z.tree.cavityLeft.Assignment) :
      nativeRestGeneratedTestValue T P.live.test
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
          (partitionPoint 0 (pre++(mid++tail)) j))
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
          (p.restRestrict (r.restRestrict (z.restRestrict σ)))
          (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed p.mark)))))=
      (((((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct σ := by
    rw [native_generated_triple_canonical_rest_product]
    apply sub_eq_zero.mp
    have H:=native_rest_generated_reset_replace_sub P.live.test P.live.ancestry ht
      (by omega) (hU.trans_le hlen)
      (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
      (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1))
        (partitionPoint 0 (pre++(mid++tail)) j))
      (p.restRestrict (r.restRestrict (z.restRestrict σ)))
      (z.tree.cavityLeft.atSlot σ (z.tree.cavityLeftSlot (z.embed (r.embed p.mark))))
    simpa only [hIn,List.map_nil,List.sum_nil,mul_zero] using H
  simp_rw [HB]
  exact E.paired_no_incoming_error_allocation ho _ c hc _ _ _
    (fun η ζ δ=>by simp only [he,hf]) d center

end OAI.SKFluctuations.Cavity
