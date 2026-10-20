module

public import ComparisonSignedCavityActualGammaPairedCanonicalSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_fresh_observed_replacement_geometry
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : NativeGeneratedTest T) {i star U : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hs : star < U) (hlen : U ≤ as.length)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P.target star).tree.markedAttach 0)
    (hhigh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark) :
    let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
    let GP:=nativeFreshObservedShape G P.target star p hp
    let js:=nativeFreshObservedReplacementSlots G P.target star p
    (∀e,G.i e≠P.target) ∧ (∀e,GP.i e≠js e) ∧
      (∀e,p.tree.splitIndex (GP.i e) (GP.j e)=p.tree.splitIndex (GP.i e) (js e)) ∧
      (∀e,GP.j e≠js e → p.tree.splitIndex (GP.j e) (js e)=
        p.tree.splitIndex (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark) := by
  dsimp only
  let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
  let g:=nativeFreshAtSlot T 0 P.target star
  have Hlow e : T.splitIndex P.target (G.i e) < U :=
    (native_generated_second_endpoint_low P hP hi (P.edges.get e) (List.get_mem _ e)).trans_lt hs
  refine ⟨?_,?_⟩
  · intro e he
    have H:=Hlow e
    rw [he,T.splitIndex_self] at H
    omega
  · apply native_marked_replacement_geometry
      (G.retainOnMarked 0 g (nativeFreshAtSlot_mem T 0 P.target star))
      (g.embed P.target) p 0 hp U hhigh
    intro e
    change g.tree.splitIndex (g.embed P.target) (g.embed (G.i e)) < U
    rw [(nativeFreshAtSlot_old_splits T 0 P.target star).2]
    exact Hlow e

theorem native_generated_paired_source_eq_endpoint_retarget
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : NativeGeneratedTest T) {i star U : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hs : star < U) (hlen : U ≤ as.length)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 P.target star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 P.target star).tree.markedAttach 0)
    (hhigh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P.target star).embed P.target)) p.mark)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : p.tree.cavityLeft.Assignment) :
    let g:=nativeFreshAtSlot T 0 P.target star
    let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
    let GP:=nativeFreshObservedShape G P.target star p hp
    let js:=nativeFreshObservedReplacementSlots G P.target star p
    let Hgeom:=native_generated_fresh_observed_replacement_geometry P hP hi hs hlen p hp hhigh
    nativeRestProjectedPairedTest T P.target star
      (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
      (nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j))) p σ=
      nativeRestEndpointDifference n p.tree (p.embed g.mark) p.mark (p.embed (g.embed P.target)) σ*
        ((GP.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct σ-
          ((GP.retarget js Hgeom.2.1).canonicalMinimumSource M
            (fun _=>NativeSourceFactorForm.centered)).restProduct σ) := by
  dsimp only
  let G:=nativeGeneratedCompleteShape n P hP hi (hs.trans_le hlen)
  have Hgeom:=native_generated_fresh_observed_replacement_geometry P hP hi hs hlen p hp hhigh
  have H:=native_paired_canonical_source_eq_endpoint_retarget G P.target star Hgeom.1 p hp
    Hgeom.2.1 Hgeom.2.2.1 M (fun _=>NativeSourceFactorForm.centered) σ
  have Heq : (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)):=
    funext (native_generated_complete_canonical_rest_product n P hP hi (hs.trans_le hlen) M)
  rw [Heq] at H
  exact H

theorem native_fresh_observed_endpoint_splits
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) {star U : ℕ} (hs : star < U) (hlen : U ≤ as.length)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0)
    (hhigh : U ≤ p.tree.splitIndex (p.embed ((nativeFreshAtSlot T 0 s star).embed s)) p.mark) :
    let g:=nativeFreshAtSlot T 0 s star
    p.tree.splitIndex (p.embed g.mark) p.mark=star ∧
      p.tree.splitIndex (p.embed g.mark) (p.embed (g.embed s))=star := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have Hstar : p.tree.splitIndex (p.embed g.mark) (p.embed (g.embed s))=star := by
    rw [(g.tree.markedAttach_embed_preserves 0 p hp).2]
    change (nativeFreshAtSlot T 0 s star).tree.splitIndex
      (nativeFreshAtSlot T 0 s star).mark ((nativeFreshAtSlot T 0 s star).embed s)=star
    rw [nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hlen)]
  refine ⟨?_,Hstar⟩
  have HL : p.tree.splitIndex (p.embed (g.embed s)) (p.embed g.mark) < U := by
    rw [p.tree.splitIndex_symm,Hstar]
    exact hs
  have HE:=p.tree.splitIndex_low_eq_of_high p.mark (p.embed (g.embed s)) (p.embed g.mark)
    (by simpa only [ClockTree.splitIndex_symm] using hhigh) HL
  simpa only [ClockTree.splitIndex_symm] using HE.trans (by simpa only [ClockTree.splitIndex_symm] using Hstar)

end OAI.SKFluctuations.Cavity
