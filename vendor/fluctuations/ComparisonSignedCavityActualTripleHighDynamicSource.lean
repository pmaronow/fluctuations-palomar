module

public import ComparisonSignedCavityActualObservedProjectionFactorization

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem ActualNaturalBoundaryShape.retainOnMarked_canonicalMinimumSource_eq
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f : Fin a→NativeSourceFactorForm) (b : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach b) :
    (G.canonicalMinimumSource M f).retainOnMarked b p hp=
      (G.retainOnMarked b p hp).canonicalMinimumSource M f := by
  unfold ActualNaturalBoundaryShape.canonicalMinimumSource ActualNaturalBoundaryShape.retainOnMarked
  congr 1 <;> funext e <;> simp only [ActualNaturalBoundaryShape.sourceLowMass,
    (T.markedAttach_embed_preserves b p hp).2]

theorem native_triple_high_dynamic_canonical_exterior_source
    (n a : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} (s : T.Slot)
    (G : ActualNaturalBoundaryShape n a T)
    {U : ℕ} (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0)
    (hpH : U ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hrH : U ≤ r.tree.splitIndex (r.embed (p.embed s)) r.mark)
    (hzH : U ≤ z.tree.splitIndex (z.embed (r.embed (p.embed s))) z.mark)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (hlow : ∀j,T.cavityLeft.splitIndex (T.cavityLeftSlot s) (G.restLabels j)
      ≤ pre.length+mid.length) :
    let G3:=((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz
    ∃E : NativeDynamicCanonicalExteriorSource n a pre mid tail z.tree
      (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed s)))) G3 v q x,
      ∃(c e f : E.D.Slot),
        (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ)
          (z.tree.cavityLeftSlot (z.embed (r.embed p.mark)))=E.D.atSlot δ c) ∧
        (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ)
          (z.tree.cavityLeftSlot (z.embed r.mark))=E.D.atSlot δ e) ∧
        (∀η ζ δ,z.tree.cavityLeft.atSlot (E.read η ζ δ)
          (z.tree.cavityLeftSlot z.mark)=E.D.atSlot δ f) ∧
        pre.length+mid.length+E.D.splitIndex E.target c=
          z.tree.splitIndex (z.embed (r.embed (p.embed s))) (z.embed (r.embed p.mark)) ∧
        pre.length+mid.length+E.D.splitIndex E.target e=
          z.tree.splitIndex (z.embed (r.embed (p.embed s))) (z.embed r.mark) ∧
        pre.length+mid.length+E.D.splitIndex E.target f=
          z.tree.splitIndex (z.embed (r.embed (p.embed s))) z.mark := by
  dsimp only
  have hpH' : U ≤ p.tree.splitIndex p.mark (p.embed s) := by
    simpa only [ClockTree.splitIndex_symm] using hpH
  have hrH' : U ≤ r.tree.splitIndex r.mark (r.embed (p.embed s)) := by
    simpa only [ClockTree.splitIndex_symm] using hrH
  have hzH' : U ≤ z.tree.splitIndex z.mark (z.embed (r.embed (p.embed s))) := by
    simpa only [ClockTree.splitIndex_symm] using hzH
  have hi : pre.length ≤ pre.length+mid.length := by omega
  have HT := (((hT.observedHigh hi hU 0 p hp s hpH').observedHigh hi hU 0 r hr
    (p.embed s) hrH').observedHigh hi hU 0 z hz (r.embed (p.embed s)) hzH').cavityLeft
  have hlen : U ≤ pre.length+mid.length+tail.length := by
    have H:=hpH.trans (p.tree.splitIndex_le_clockLength _ _)
    simp only [List.length_append] at H
    omega
  have Hlow (j : Fin a×Bool) :
      z.tree.cavityLeft.splitIndex (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed s))))
        ((((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).restLabels j)
          ≤ pre.length+mid.length := by
    simp only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.retainOnMarked,
      ClockTree.cavityLeft_splitIndex]
    rw [←apply_ite z.embed,←apply_ite r.embed,←apply_ite p.embed,
      (r.tree.markedAttach_embed_preserves 0 z hz).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    simpa only [ActualNaturalBoundaryShape.restLabels,ClockTree.cavityLeft_splitIndex] using hlow j
  obtain ⟨E⟩:=native_dynamic_canonical_exterior_source n a pre mid tail z.tree
    (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed s))))
    (((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz)
    hmid hU hlen HT ho v q x Hlow
  have Hc : pre.length+mid.length < z.tree.cavityLeft.splitIndex
      (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed s))))
      (z.tree.cavityLeftSlot (z.embed (r.embed p.mark))) := by
    rw [ClockTree.cavityLeft_splitIndex,(r.tree.markedAttach_embed_preserves 0 z hz).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2]
    exact hU.trans_le hpH
  have He : pre.length+mid.length < z.tree.cavityLeft.splitIndex
      (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed s))))
      (z.tree.cavityLeftSlot (z.embed r.mark)) := by
    rw [ClockTree.cavityLeft_splitIndex,(r.tree.markedAttach_embed_preserves 0 z hz).2]
    exact hU.trans_le hrH
  have Hf : pre.length+mid.length < z.tree.cavityLeft.splitIndex
      (z.tree.cavityLeftSlot (z.embed (r.embed (p.embed s))))
      (z.tree.cavityLeftSlot z.mark) := by
    simpa only [ClockTree.cavityLeft_splitIndex] using hU.trans_le hzH
  obtain ⟨c,hc,hcs⟩:=E.high _ Hc
  obtain ⟨e,he,hes⟩:=E.high _ He
  obtain ⟨f,hf,hfs⟩:=E.high _ Hf
  exact ⟨E,c,e,f,hc,he,hf,by simpa only [ClockTree.cavityLeft_splitIndex] using hcs,
    by simpa only [ClockTree.cavityLeft_splitIndex] using hes,
    by simpa only [ClockTree.cavityLeft_splitIndex] using hfs⟩

theorem native_actual_generated_triple_high_dynamic_exterior_source
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
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    let hlen : U ≤ (pre++(mid++tail)).length :=
      hpH.trans (p.tree.splitIndex_le_clockLength _ _)
    let G:=nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)
    let G3:=((((G.retainOnMarked 0 p hp).retainOnMarked 0 r hr).retainOnMarked 0 z hz).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered))
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
  rw [←ActualNaturalBoundaryShape.retainOnMarked_canonicalMinimumSource_eq,
    ←ActualNaturalBoundaryShape.retainOnMarked_canonicalMinimumSource_eq,
    ←ActualNaturalBoundaryShape.retainOnMarked_canonicalMinimumSource_eq]
  apply native_triple_high_dynamic_canonical_exterior_source n _ pre mid tail
    P.live.test.target _ hmid hU (hP.persistentLowForks (by omega)) p hp r hr z hz
    hpH hrH hzH ho v q x
  intro j
  simpa only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.canonicalMinimumSource]
    using native_generated_exterior_shape_labels_low n P.live.test P.live.ancestry
      (by omega) (hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))) j

end OAI.SKFluctuations.Cavity
