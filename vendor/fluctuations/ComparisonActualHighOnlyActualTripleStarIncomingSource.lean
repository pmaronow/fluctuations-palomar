module

public import ComparisonActualHighOnlyActualTripleHighDynamicSource
public import ComparisonSignedCavityActualTripleStarIncomingSource
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyGeneratedTripleReset

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_triple_reset_incoming_star_error_source_high_only
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (ht : P.live.test.teeth=[]) (e₀ : T.Slot) (hIn : P.live.test.incoming=[e₀])
    (hi : T.splitIndex P.live.test.target e₀=pre.length+mid.length)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark)
    (hrH : U ≤ r.tree.splitIndex (r.embed (p.embed P.live.test.target)) r.mark)
    (hzH : U ≤ z.tree.splitIndex (z.embed (r.embed (p.embed P.live.test.target))) z.mark)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (d : ℕ) (center : ℝ) :
    let as:=pre++(mid++tail)
    let hlen : pre.length+mid.length < as.length:=
      hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))
    let G:=((((nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)
    let G₀:=((((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalHighOnlySource M (fun _=>NativeSourceFactorForm.centered)
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
    ∃(c e f : E.D.Slot) (i₀ : E.Es.Slot),
      (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ) c₀=E.D.atSlot δ c) ∧
      (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ) e₁=E.D.atSlot δ e) ∧
      (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ) e₂=E.D.atSlot δ f) ∧
      (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ)
        (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed e₀))))=E.Es.atSlot ζ i₀) ∧
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
      (∫w,nativeTwoLevelStarIncomingErrorProduct n 0 d E.Ei E.Es E.D E.H i₀ E.target c qi qs center error
        (exteriorForestIRoot w) (exteriorForestStarRoot w)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)+
      ∑j∈Finset.range d,∫w,nativeTwoLevelPowerErrorProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>G₀.restProduct (E.read η ζ δ)) E.target c qi qs center error
        (exteriorForestIRoot w) (exteriorForestStarRoot w)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  have hlen : U ≤ (pre++(mid++tail)).length:=hpH.trans (p.tree.splitIndex_le_clockLength _ _)
  obtain ⟨E,c,e,f,hc,he,hf,hcs,_hes,_hfs⟩:=
    native_actual_generated_triple_high_dynamic_exterior_source_high_only n pre mid tail hP hmid hU
      p hp r hr z hz hpH hrH hzH ho M v q x
  have hlow : z.tree.cavityLeft.splitIndex
      (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed P.live.test.target))))
      (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed e₀))))=pre.length+mid.length := by
    rw [cavityLeft_splitIndex,(r.tree.markedAttach_embed_preserves 0 z hz).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2,hi]
  obtain ⟨i₀,hi₀⟩:=E.incoming_star _ hlow
  refine ⟨E,c,e,f,i₀,hc,he,hf,hi₀,hcs,?_⟩
  apply E.paired_incoming_star_error_allocation ho _ _ c i₀ hc hi₀ _ _ _ _
    (fun η ζ δ=>by simp only [he,hf])
    (fun σ=>native_generated_triple_reset_change_high_only n P.live.test P.live.ancestry ht
      (by omega) (hU.trans_le hlen) e₀ hIn M p hp r hr z hz σ) d center

end OAI.SKFluctuations.Cavity
