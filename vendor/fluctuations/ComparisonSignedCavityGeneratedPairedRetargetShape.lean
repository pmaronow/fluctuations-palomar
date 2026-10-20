module

public import ComparisonSignedCavityGeneratedCompleteShape
public import ComparisonSignedCavityPairedRawResampling
public import ComparisonSignedCavityActualMarkedExchange

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_second_endpoint_low {S : Type} {as : List PositiveMass}
    {T : ClockTree S as} (P : NativeGeneratedTest T) {i star : ℕ}
    (hP : NativeGeneratedTestAncestry i star P) (hi : i ≤ star)
    (e : T.Slot×T.Slot) (he : e∈P.edges) : T.splitIndex P.target e.2 ≤ star := by
  simp only [NativeGeneratedTest.edges,List.mem_append,List.mem_map] at he
  rcases he with (he|⟨c,hc,rfl⟩)|⟨c,hc,rfl⟩
  · exact (hP.exterior_departure e he).2
  · exact (hP.teeth_star c hc).le
  · change T.splitIndex P.target c ≤ star
    rcases hP.incoming_cuts c hc with h|h <;> omega

def nativeMarkedReplacementSlots {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (s : T.Slot) (p : MarkedPlacement T) : Fin a → p.tree.Slot := by
  classical
  exact fun e=>if G.j e=s then p.mark else p.embed (G.j e)

theorem native_marked_replacement_geometry {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (s : T.Slot) (p : MarkedPlacement T) (r : ℝ) (hp : p∈T.markedAttach r)
    (U : ℕ) (hhigh : U ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hlow : ∀e,T.splitIndex s (G.i e) < U) :
    let GP:=G.retainOnMarked r p hp
    let js:=nativeMarkedReplacementSlots G s p
    (∀e,GP.i e≠js e) ∧
      (∀e,p.tree.splitIndex (GP.i e) (GP.j e)=p.tree.splitIndex (GP.i e) (js e)) ∧
      (∀e,GP.j e≠js e →
        p.tree.splitIndex (GP.j e) (js e)=p.tree.splitIndex (p.embed s) p.mark) := by
  classical
  dsimp only
  have Hlow e : p.tree.splitIndex (p.embed s) (p.embed (G.i e)) < U := by
    rw [(T.markedAttach_embed_preserves r p hp).2]
    exact hlow e
  have HE e : p.tree.splitIndex (p.embed (G.i e)) p.mark=
      p.tree.splitIndex (p.embed (G.i e)) (p.embed s) := by
    rw [p.tree.splitIndex_symm (p.embed (G.i e)) p.mark,
      p.tree.splitIndex_symm (p.embed (G.i e)) (p.embed s)]
    exact p.tree.splitIndex_low_eq_of_high p.mark (p.embed s) (p.embed (G.i e))
      (by simpa only [ClockTree.splitIndex_symm] using hhigh) (Hlow e)
  refine ⟨?_,?_,?_⟩
  · intro e
    dsimp only [nativeMarkedReplacementSlots,ActualNaturalBoundaryShape.retainOnMarked]
    split_ifs with hj
    · intro hc
      have HL:=Hlow e
      rw [hc] at HL
      omega
    · exact fun H=>G.distinct e ((T.markedAttach_embed_preserves r p hp).1 H)
  · intro e
    dsimp only [nativeMarkedReplacementSlots,ActualNaturalBoundaryShape.retainOnMarked]
    split_ifs with hj
    · rw [hj,HE e]
    · rfl
  · intro e he
    dsimp only [nativeMarkedReplacementSlots,ActualNaturalBoundaryShape.retainOnMarked] at he ⊢
    split_ifs at he ⊢ with hj
    · rw [hj]
    · exact False.elim (he rfl)

theorem native_generated_marked_replacement_geometry
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : NativeGeneratedTest T) {i star U : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hs : star < U) (hlen : U ≤ as.length)
    (p : MarkedPlacement T) (r : ℝ) (hp : p∈T.markedAttach r)
    (hhigh : U ≤ p.tree.splitIndex (p.embed P.target) p.mark) :
    let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
    let GP:=G.retainOnMarked r p hp
    let js:=nativeMarkedReplacementSlots G P.target p
    (∀e,GP.i e≠js e) ∧
      (∀e,p.tree.splitIndex (GP.i e) (GP.j e)=p.tree.splitIndex (GP.i e) (js e)) ∧
      (∀e,GP.j e≠js e →
        p.tree.splitIndex (GP.j e) (js e)=p.tree.splitIndex (p.embed P.target) p.mark) := by
  dsimp only
  apply native_marked_replacement_geometry _ P.target p r hp U hhigh
  intro e
  exact (native_generated_second_endpoint_low P hP hi (P.edges.get e) (List.get_mem _ e)).trans_lt hs

theorem ActualNaturalBoundaryShape.marked_retarget_restProduct
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot)
    (hfixed : ∀e,G.i e≠s) (p : MarkedPlacement T) (r : ℝ) (hp : p∈T.markedAttach r)
    (hne : ∀e,(G.retainOnMarked r p hp).i e≠nativeMarkedReplacementSlots G s p e)
    (σ : p.tree.cavityLeft.Assignment) :
    ((G.retainOnMarked r p hp).retarget (nativeMarkedReplacementSlots G s p) hne).restProduct σ=
      G.restProduct (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s)
        (p.restRestrict σ) (p.restSpin σ)) := by
  classical
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  have HI : T.cavityLeftSlot (G.i e)≠T.cavityLeftSlot s:=
    fun H=>hfixed e (T.cavityLeftSlot.injective H)
  simp only [retarget,retainOnMarked,nativeMarkedReplacementSlots,nativeReplaceAtSlot_at,
    ite_eq_right HI,p.restRestrict_at]
  by_cases hj : G.j e=s
  · have HJ : T.cavityLeftSlot (G.j e)=T.cavityLeftSlot s:=congrArg T.cavityLeftSlot hj
    simp only [hj,ite_true]
    rfl
  · have HJ : T.cavityLeftSlot (G.j e)≠T.cavityLeftSlot s:=
      fun H=>hj (T.cavityLeftSlot.injective H)
    simp only [ite_eq_right hj,ite_eq_right HJ]

theorem ActualNaturalBoundaryShape.marked_retarget_canonical_restProduct
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot)
    (hfixed : ∀e,G.i e≠s) (p : MarkedPlacement T) (r : ℝ) (hp : p∈T.markedAttach r)
    (hne : ∀e,(G.retainOnMarked r p hp).i e≠nativeMarkedReplacementSlots G s p e)
    (hlow : ∀e,p.tree.splitIndex ((G.retainOnMarked r p hp).i e)
      ((G.retainOnMarked r p hp).j e)=p.tree.splitIndex ((G.retainOnMarked r p hp).i e)
        (nativeMarkedReplacementSlots G s p e))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f : Fin a → NativeSourceFactorForm) (σ : p.tree.cavityLeft.Assignment) :
    (((G.retainOnMarked r p hp).retarget (nativeMarkedReplacementSlots G s p) hne).canonicalMinimumSource M f).restProduct σ=
      (G.canonicalMinimumSource M f).restProduct
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) (p.restSpin σ)) := by
  rw [(G.retainOnMarked r p hp).retarget_canonicalMinimumSource M f _ hne hlow]
  have H:=(G.canonicalMinimumSource M f).marked_retarget_restProduct s hfixed p r hp hne σ
  simpa only [restProduct,retarget,canonicalMinimumSource,retainOnMarked,sourceLowMass,nativeMarkedReplacementSlots,
    (T.markedAttach_embed_preserves r p hp).2] using H

theorem native_generated_marked_canonical_replacement
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : NativeGeneratedTest T) {i star U : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hs : star < U) (hlen : U ≤ as.length)
    (p : MarkedPlacement T) (r : ℝ) (hp : p∈T.markedAttach r)
    (hhigh : U ≤ p.tree.splitIndex (p.embed P.target) p.mark)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : p.tree.cavityLeft.Assignment) :
    let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
    let Hg:=native_generated_marked_replacement_geometry P hP hi hs hlen p r hp hhigh
    (((G.retainOnMarked r p hp).retarget (nativeMarkedReplacementSlots G P.target p) Hg.1).canonicalMinimumSource
      M (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j))
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ)) := by
  dsimp only
  let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
  have Hfixed e : G.i e≠P.target := by
    intro he
    have HL:=native_generated_second_endpoint_low P hP hi (P.edges.get e) (List.get_mem _ e)
    change T.splitIndex P.target (G.i e) ≤ star at HL
    rw [he,T.splitIndex_self] at HL
    omega
  rw [ActualNaturalBoundaryShape.marked_retarget_canonical_restProduct _ P.target Hfixed p r hp
    (native_generated_marked_replacement_geometry P hP hi hs hlen p r hp hhigh).1
    (native_generated_marked_replacement_geometry P hP hi hs hlen p r hp hhigh).2.1]
  exact native_generated_complete_canonical_rest_product n P hP hi (hs.trans_le hlen) M _

end OAI.SKFluctuations.Cavity
