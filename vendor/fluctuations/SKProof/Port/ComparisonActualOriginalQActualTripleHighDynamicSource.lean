module

public import ComparisonSignedCavityActualTripleHighDynamicSource
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 16000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_generated_triple_high_dynamic_exterior_source_original_q
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark)
    (hrH : U ≤ r.tree.splitIndex (r.embed (p.embed P.live.test.target)) r.mark)
    (hzH : U ≤ z.tree.splitIndex (z.embed (r.embed (p.embed P.live.test.target))) z.mark)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    let hlen : U ≤ (pre++(mid++tail)).length :=
      hpH.trans (p.tree.splitIndex_le_clockLength _ _)
    let G:=nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)
    let G3:=((((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered))
    ∃E : NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail z.tree
      (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed P.live.test.target)))) G3 v q x,
      ∃(c e f : E.D.Slot),
        (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ)
          (z.tree.cavityLeftSlot (z.embed (r.embed p.mark)))=E.D.atSlot δ c) ∧
        (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ)
          (z.tree.cavityLeftSlot (z.embed r.mark))=E.D.atSlot δ e) ∧
        (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ)
          (z.tree.cavityLeftSlot z.mark)=E.D.atSlot δ f) ∧
        pre.length+mid.length+E.D.splitIndex E.target c=
          z.tree.splitIndex (z.embed (r.embed (p.embed P.live.test.target))) (z.embed (r.embed p.mark)) ∧
        pre.length+mid.length+E.D.splitIndex E.target e=
          z.tree.splitIndex (z.embed (r.embed (p.embed P.live.test.target))) (z.embed r.mark) ∧
        pre.length+mid.length+E.D.splitIndex E.target f=
          z.tree.splitIndex (z.embed (r.embed (p.embed P.live.test.target))) z.mark := by
  exact actual_general_generated_triple_high_dynamic_exterior_source n pre mid tail hP hmid hU
    p hp r hr z hz hpH hrH hzH ho M.sweepBf M.sweepHf v q x

end OAI.SKFluctuations.Cavity
