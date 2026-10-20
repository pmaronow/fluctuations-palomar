module

public import ComparisonSignedCavityForestClassificationLaw
public import ComparisonSignedCavityRetainedSubtreeClone

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

theorem nativeCloneBlockAtSlot_slot_coverage {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ)
    (c : (nativeCloneBlockAtSlot T s j).tree.Slot) :
    (∃d,c=(nativeCloneBlockAtSlot T s j).oldEmbed d) ∨
      (∃d,c=(nativeCloneBlockAtSlot T s j).newEmbed d) := by
  induction T generalizing j with
  | leaf=>
    cases j with
    | zero=>cases c with
      | inl d=>exact Or.inl ⟨d,rfl⟩
      | inr d=>exact Or.inr ⟨d,rfl⟩
    | succ j=>exact Or.inl ⟨c,rfl⟩
  | step b T ih=>
    cases j with
    | zero=>cases c with
      | inl d=>exact Or.inl ⟨d,rfl⟩
      | inr d=>exact Or.inr ⟨d,rfl⟩
    | succ j=>exact ih s j c
  | fork T V ihT ihV=>
    cases j with
    | zero=>cases c with
      | inl d=>exact Or.inl ⟨d,rfl⟩
      | inr d=>exact Or.inr ⟨d,rfl⟩
    | succ j=>cases s with
      | inl s=>cases c with
        | inl c=>
          rcases ihT s (j+1) c with ⟨d,h⟩|⟨d,h⟩
          · exact Or.inl ⟨Sum.inl d,congrArg Sum.inl h⟩
          · exact Or.inr ⟨Sum.inl d,congrArg Sum.inl h⟩
        | inr c=>exact Or.inl ⟨Sum.inr c,rfl⟩
      | inr s=>cases c with
        | inl c=>exact Or.inl ⟨Sum.inl c,rfl⟩
        | inr c=>
          rcases ihV s (j+1) c with ⟨d,h⟩|⟨d,h⟩
          · exact Or.inl ⟨Sum.inr d,congrArg Sum.inr h⟩
          · exact Or.inr ⟨Sum.inr d,congrArg Sum.inr h⟩

theorem NativePersistentLowForks.retainedClone {as : List PositiveMass}
    {T : ClockTree S as} {i star U : ℕ} (hT : NativePersistentLowForks i star U T)
    (s : T.Slot) (cut : ℕ) (hcut : U≤cut) :
    NativePersistentLowForks i star U (nativeCloneBlockAtSlot T s cut).tree := by
  intro c d
  rcases nativeCloneBlockAtSlot_slot_coverage T s cut c with ⟨c,rfl⟩|⟨c,rfl⟩
  · rcases nativeCloneBlockAtSlot_slot_coverage T s cut d with ⟨d,rfl⟩|⟨d,rfl⟩
    · rw [(nativeCloneBlockAtSlot_within_copy_splits T s cut c d).1]
      exact hT c d
    · rw [nativeCloneBlockAtSlot_cross_split]
      split_ifs
      · exact Or.inr (Or.inr hcut)
      · exact hT c d
  · rcases nativeCloneBlockAtSlot_slot_coverage T s cut d with ⟨d,rfl⟩|⟨d,rfl⟩
    · rw [splitIndex_symm,nativeCloneBlockAtSlot_cross_split]
      split_ifs
      · exact Or.inr (Or.inr hcut)
      · exact hT d c
    · rw [(nativeCloneBlockAtSlot_within_copy_splits T s cut c d).2]
      exact hT c d

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_classified_retained_clone_four_tooth
    (pre mid tail : List PositiveMass) (T : ClockTree S (pre++(mid++tail))) (s : T.Slot)
    {U cut : ℕ} (hU : pre.length+mid.length<U)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hhigh : U≤cut) (hcut : cut≤(pre++(mid++tail)).length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    let C:=nativeCloneBlockAtSlot T s cut
    ∃(Ei : ClockTree S (mid++tail)) (Es D : ClockTree S tail)
      (read : Ei.Assignment → Es.Assignment → D.Assignment → C.tree.Assignment) (old new : D.Slot),
      (∀η ζ σ,T.atSlot (C.oldRestrict (read η ζ σ)) s=D.atSlot σ old) ∧
      (∀η ζ σ,T.atSlot (C.newRestrict (read η ζ σ)) s=D.atSlot σ new) ∧
      (pre.length+mid.length+D.splitIndex old new=cut) ∧
      (∀c,¬cut≤T.splitIndex s c → ∀η ζ σ,
        T.atSlot (C.oldRestrict (read η ζ σ)) c=T.atSlot (C.newRestrict (read η ζ σ)) c) ∧
      (∀Q : T.Assignment → T.Assignment → ℝ,
        C.tree.disorderExpect w φ v q (fun σ=>Q (C.oldRestrict σ) (C.newRestrict σ)) x=
          ∫z,nativeExteriorForestConditionalTest Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ σ=>Q (C.oldRestrict (read η ζ σ)) (C.newRestrict (read η ζ σ)))
            (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) ∧
      (∀Q : T.Assignment → T.Assignment → ℝ,
        let F:=fun η ζ σ=>Q (C.oldRestrict (read η ζ σ)) (C.newRestrict (read η ζ σ))
        (nativeExteriorForestTree pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D).disorderExpect w φ v q
          (nativeExteriorForestRead pre mid (exteriorQuadNative Ei) (exteriorQuadNative Es) D
            (fun η ζ σ=>F η.1.1 ζ.1.1 σ*F η.1.2 ζ.1.2 σ*
              F η.2.1 ζ.2.1 σ*F η.2.2 ζ.2.2 σ)) x=
          ∫z,nativeExteriorForestAveragedFourth Ei Es D w φ
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            F (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw w φ pre mid tail v q x) := by
  let C:=nativeCloneBlockAtSlot T s cut
  have hC:=hT.retainedClone s cut hhigh
  have hc : C.tree.splitIndex (C.oldEmbed s) (C.newEmbed s)=cut := by
    rw [nativeCloneBlockAtSlot_cross_split,T.splitIndex_self,ite_eq_left ⟨hcut,hcut⟩]
  obtain ⟨Ei,Es,D,R,d,ht,hh,hfirst,hfour⟩:=native_classified_source_and_four_tooth_disorder
    pre mid tail C.tree (C.oldEmbed s) hU hC hw φ ho v q x
  obtain ⟨f,hf,hsplit⟩:=hh (C.newEmbed s) (by rw [hc];omega)
  refine ⟨Ei,Es,D,R,d,f,?_,?_,?_,?_,?_,?_⟩
  · intro η ζ σ
    rw [C.old_at]
    exact ht η ζ σ
  · intro η ζ σ
    rw [C.new_at]
    exact hf η ζ σ
  · exact hsplit.trans hc
  · intro c hout η ζ σ
    exact nativeCloneBlockAtSlot_exterior_observation_shared T s cut c (Nat.lt_of_not_ge hout) (R η ζ σ)
  · intro Q
    exact hfirst (fun σ=>Q (C.oldRestrict σ) (C.newRestrict σ))
  · intro Q
    exact hfour (fun σ=>Q (C.oldRestrict σ) (C.newRestrict σ))

end OAI.SKFluctuations.Cavity
