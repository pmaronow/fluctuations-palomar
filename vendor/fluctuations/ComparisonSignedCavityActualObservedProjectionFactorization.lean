module

public import ComparisonSignedCavityObservedProjectionSpine
public import ComparisonSignedCavityDynamicCanonicalExteriorSource
public import ComparisonSignedCavityActualGeneratedExteriorSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 20000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]
variable {as : List PositiveMass}

theorem native_actual_generated_observed_projection_power_law
    {T : ClockTree (S×B) as} {i star U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : star<p.tree.splitIndex (p.embed P.live.test.target) p.mark)
    (R : S→S→ℝ) (C : ℕ→ℝ) :
    ∃(A : ClockTree (S×B) as) (base : NativeResourceTerm i star A)
      (seed₀ : List NativeResourceMark) (k₀ : ℕ),
      NativeActualResourceGenerated i star U seed₀ k₀ A base ∧
      base.live.test.teeth=[] ∧ base.live.test.incoming.length≤1 ∧
      ∃spine : NativeProjectionSpine base.live.test star P.live.test,
      ∃r : MarkedPlacement A,r∈A.markedAttach 0 ∧ p.coeff=r.coeff ∧
        p.tree.splitIndex (p.embed P.live.test.target) p.mark=
          r.tree.splitIndex (r.embed base.live.test.target) r.mark ∧
      (∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ),
        nativeStarFieldTestMean w φ p.tree.cavityLeft
          (p.tree.cavityLeftSlot (p.embed P.live.test.target)) star q
          (fun y σ=>J y (spine.restRead (p.restRestrict σ)) (p.restSpin σ)*
            nativeRestGeneratedTestValue T P.live.test R C (p.restRestrict σ)) x=
        nativeStarFieldTestMean w φ r.tree.cavityLeft
          (r.tree.cavityLeftSlot (r.embed base.live.test.target)) star q
          (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
            nativeRestGeneratedTestValue A base.live.test R C (r.restRestrict σ)*
            (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
              (A.cavityLeft.atSlot (r.restRestrict σ) (A.cavityLeftSlot base.live.test.target)))^
                P.live.test.teeth.length) x) ∧
      (∀(q : ℕ→ι→ℝ≥0) (J : (ι→ℝ)→A.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ),
        nativeStarFieldTestMean w φ p.tree.cavityLeft
          (p.tree.cavityLeftSlot (p.embed P.live.test.target)) star q
          (fun y σ=>J y (spine.restRead (p.restRestrict σ)) (p.restSpin σ)*
            nativeRestGeneratedTestValue T P.live.test R C
              (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
                (p.restRestrict σ) (p.restSpin σ))) x=
        nativeStarFieldTestMean w φ r.tree.cavityLeft
          (r.tree.cavityLeftSlot (r.embed base.live.test.target)) star q
          (fun y σ=>J y (r.restRestrict σ) (r.restSpin σ)*
            nativeRestGeneratedTestValue A base.live.test R C
              (nativeReplaceAtSlot A.cavityLeft (A.cavityLeftSlot base.live.test.target)
                (r.restRestrict σ) (r.restSpin σ))*
            (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y (r.restSpin σ))^
              P.live.test.teeth.length) x) := by
  obtain ⟨A,base,seed₀,k₀,hBase,ht,⟨spine⟩⟩:=hP.projectionDecomposition
  have hc:=spine.teeth_length
  rw [ht,List.length_nil,Nat.zero_add] at hc
  obtain ⟨r,hr,hcoeff,hsplit,hOld,hNew⟩:=spine.observed_paired_rest_factorization
    (hBase.targetStarSingleton hi) (hP.targetStarSingleton hi) hw φ 0 ho p hp hh R C
  refine ⟨A,base,seed₀,k₀,hBase,ht,base.live.ancestry.incoming_degree,
    spine,r,hr,hcoeff,hsplit,?_⟩
  simpa only [←hc] using And.intro hOld hNew

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_observed_generated_dynamic_exterior_source
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c))
    (hc : U≤T.splitIndex c P.live.test.target)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    let hlen : U≤(pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
    let G:=nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)
    Nonempty (NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed c))
      ((G.retainOnMarked a p hp).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)) v q x) := by
  dsimp only
  apply native_actual_generated_dynamic_canonical_exterior_source n _ pre mid tail hP hmid hU a p hp c hh ho
  intro j
  simpa only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.canonicalMinimumSource]
    using native_generated_exterior_marked_labels_low n P.live.test P.live.ancestry
      (by omega) hU (hh.trans (p.tree.splitIndex_le_clockLength _ _)) a p hp c hc j

end OAI.SKFluctuations.Cavity
