module

public import ComparisonSignedCavityCanonicalMarkedOldProduct
public import ComparisonSignedCavityCanonicalRestFactorMoments
public import ComparisonSignedCavityRetainedSubtreeClone

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type*} {as : List PositiveMass} {T : ClockTree (S×B) as}
namespace NativeRetainedSubtreeClone

def restOldRestrict (p : NativeRetainedSubtreeClone T) (σ : p.tree.cavityLeft.Assignment) :
    T.cavityLeft.Assignment := assignmentOfSlots T.cavityLeft (fun s=>
      p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.oldEmbed (T.cavityLeftSlot.symm s))))

def restNewRestrict (p : NativeRetainedSubtreeClone T) (σ : p.tree.cavityLeft.Assignment) :
    T.cavityLeft.Assignment := assignmentOfSlots T.cavityLeft (fun s=>
      p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.newEmbed (T.cavityLeftSlot.symm s))))

theorem restOldRestrict_at (p : NativeRetainedSubtreeClone T)
    (σ : p.tree.cavityLeft.Assignment) (s : T.Slot) :
    T.cavityLeft.atSlot (p.restOldRestrict σ) (T.cavityLeftSlot s)=
      p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.oldEmbed s)) := by
  simp only [restOldRestrict,atSlot_assignmentOfSlots,Equiv.symm_apply_apply]

theorem restNewRestrict_at (p : NativeRetainedSubtreeClone T)
    (σ : p.tree.cavityLeft.Assignment) (s : T.Slot) :
    T.cavityLeft.atSlot (p.restNewRestrict σ) (T.cavityLeftSlot s)=
      p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.newEmbed s)) := by
  simp only [restNewRestrict,atSlot_assignmentOfSlots,Equiv.symm_apply_apply]

theorem restOldRestrict_actual (p : NativeRetainedSubtreeClone T) (σ : p.tree.Assignment) :
    (T.cavityAssignment (p.oldRestrict σ)).1=p.restOldRestrict (p.tree.cavityAssignment σ).1 := by
  apply T.cavityLeft.assignment_ext
  intro s
  obtain ⟨s,rfl⟩:=T.cavityLeftSlot.surjective s
  rw [atSlot_cavityLeft,restOldRestrict_at,atSlot_cavityLeft,p.old_at]

theorem restNewRestrict_actual (p : NativeRetainedSubtreeClone T) (σ : p.tree.Assignment) :
    (T.cavityAssignment (p.newRestrict σ)).1=p.restNewRestrict (p.tree.cavityAssignment σ).1 := by
  apply T.cavityLeft.assignment_ext
  intro s
  obtain ⟨s,rfl⟩:=T.cavityLeftSlot.surjective s
  rw [atSlot_cavityLeft,restNewRestrict_at,atSlot_cavityLeft,p.new_at]

end NativeRetainedSubtreeClone
end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 15000000
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def onCloneOld (G : ActualNaturalBoundaryShape n a T) (target : T.Slot) (cut : ℕ) :
    ActualNaturalBoundaryShape n a (nativeCloneBlockAtSlot T target cut).tree where
  α:=G.α
  β:=G.β
  i:=fun e=>(nativeCloneBlockAtSlot T target cut).oldEmbed (G.i e)
  j:=fun e=>(nativeCloneBlockAtSlot T target cut).oldEmbed (G.j e)
  distinct:=fun e H=>G.distinct e ((nativeCloneBlockAtSlot_embed_injective T target cut).1 H)
  lowInGrid:=fun e=>by
    rw [(nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]
    exact G.lowInGrid e

theorem onCloneOld_sourceLowMass (G : ActualNaturalBoundaryShape n a T)
    (target : T.Slot) (cut : ℕ) (e : Fin a) :
    (G.onCloneOld target cut).sourceLowMass e=G.sourceLowMass e := by
  unfold sourceLowMass onCloneOld
  rw [(nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]

theorem onCloneOld_restProduct (G : ActualNaturalBoundaryShape n a T)
    (target : T.Slot) (cut : ℕ)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    (G.onCloneOld target cut).restProduct σ=
      G.restProduct ((nativeCloneBlockAtSlot T target cut).restOldRestrict σ) := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [onCloneOld,NativeRetainedSubtreeClone.restOldRestrict_at]

theorem onCloneOld_canonical_restProduct
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (target : T.Slot) (cut : ℕ)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    ((G.onCloneOld target cut).canonicalMinimumSource M forms).restProduct σ=
      (G.canonicalMinimumSource M forms).restProduct
        ((nativeCloneBlockAtSlot T target cut).restOldRestrict σ) := by
  rw [←(G.canonicalMinimumSource M forms).onCloneOld_restProduct target cut σ]
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalMinimumSource,onCloneOld,sourceLowMass,
    (nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]

theorem clone_new_targets_ne (G : ActualNaturalBoundaryShape n a T)
    (target : T.Slot) (cut : ℕ) (hout : ∀e,T.splitIndex target (G.i e)<cut) :
    ∀e,(G.onCloneOld target cut).i e≠(nativeCloneBlockAtSlot T target cut).newEmbed (G.j e) := by
  intro e H
  have he:=nativeCloneBlockAtSlot_exterior_shared T target cut (G.i e) (hout e)
  exact G.distinct e ((nativeCloneBlockAtSlot_embed_injective T target cut).2 (he.symm.trans H))

theorem clone_new_targets_same_low (G : ActualNaturalBoundaryShape n a T)
    (target : T.Slot) (cut : ℕ) (hout : ∀e,T.splitIndex target (G.i e)<cut) :
    ∀e,(nativeCloneBlockAtSlot T target cut).tree.splitIndex
        ((G.onCloneOld target cut).i e) ((G.onCloneOld target cut).j e)=
      (nativeCloneBlockAtSlot T target cut).tree.splitIndex
        ((G.onCloneOld target cut).i e) ((nativeCloneBlockAtSlot T target cut).newEmbed (G.j e)) := by
  intro e
  change _= (nativeCloneBlockAtSlot T target cut).tree.splitIndex
    ((nativeCloneBlockAtSlot T target cut).oldEmbed (G.i e))
    ((nativeCloneBlockAtSlot T target cut).newEmbed (G.j e))
  rw [nativeCloneBlockAtSlot_cross_split,ite_eq_right]
  · exact (nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1
  · exact fun H=>(not_le.mpr (hout e)) H.1

theorem onCloneOld_retarget_new_canonical_restProduct
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (target : T.Slot) (cut : ℕ) (hout : ∀e,T.splitIndex target (G.i e)<cut)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    (((G.onCloneOld target cut).retarget
      (fun e=>(nativeCloneBlockAtSlot T target cut).newEmbed (G.j e))
      (G.clone_new_targets_ne target cut hout)).canonicalMinimumSource M forms).restProduct σ=
      (G.canonicalMinimumSource M forms).restProduct
        ((nativeCloneBlockAtSlot T target cut).restNewRestrict σ) := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  have Hlow:=G.clone_new_targets_same_low target cut hout e
  have hanchor:=nativeCloneBlockAtSlot_exterior_shared T target cut (G.i e) (hout e)
  simp only [canonicalMinimumSource,ActualNaturalBoundaryShape.retarget,onCloneOld,
    sourceLowMass] at Hlow ⊢
  rw [←Hlow,(nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]
  rw [NativeRetainedSubtreeClone.restNewRestrict_at,NativeRetainedSubtreeClone.restNewRestrict_at]
  rw [hanchor]

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
