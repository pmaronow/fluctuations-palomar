module

public import ComparisonActualGeneralCanonicalMarkedReset
public import ComparisonSignedCavityActualTripleHighDynamicSource

@[expose] public section
noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set Classical
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem ActualNaturalBoundaryShape.retainOnMarked_canonicalPhysicalSource_eq
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    (bf hf : ℝ→ℝ≥0)
    (f : Fin a→NativeSourceFactorForm) (b : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach b) :
    (G.canonicalPhysicalSource bf hf f).retainOnMarked b p hp=
      (G.retainOnMarked b p hp).canonicalPhysicalSource bf hf f := by
  unfold ActualNaturalBoundaryShape.canonicalPhysicalSource ActualNaturalBoundaryShape.retainOnMarked
  congr 1 <;> funext e <;> simp only [ActualNaturalBoundaryShape.sourceLowMass,
    (T.markedAttach_embed_preserves b p hp).2]

theorem actual_general_generated_triple_high_dynamic_exterior_source
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
    (bf hf : ℝ→ℝ≥0)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    let hlen : U ≤ (pre++(mid++tail)).length :=
      hpH.trans (p.tree.splitIndex_le_clockLength _ _)
    let G:=nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)
    let G3:=((((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalPhysicalSource bf hf (fun _=>NativeSourceFactorForm.centered))
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
  dsimp only
  rw [←ActualNaturalBoundaryShape.retainOnMarked_canonicalPhysicalSource_eq,
    ←ActualNaturalBoundaryShape.retainOnMarked_canonicalPhysicalSource_eq,
    ←ActualNaturalBoundaryShape.retainOnMarked_canonicalPhysicalSource_eq]
  apply native_triple_high_dynamic_canonical_exterior_source n _ pre mid tail
    P.live.test.target _ hmid hU (hP.persistentLowForks (by omega)) p hp r hr z hz
    hpH hrH hzH ho v q x
  intro j
  simpa only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.canonicalPhysicalSource]
    using native_generated_exterior_shape_labels_low n P.live.test P.live.ancestry
      (by omega) (hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))) j

end OAI.SKFluctuations.Cavity
