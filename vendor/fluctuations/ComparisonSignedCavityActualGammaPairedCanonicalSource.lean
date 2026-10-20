module

public import ComparisonSignedCavityGeneratedPairedRetargetShape
public import ComparisonSignedCavityActualGammaFirstHighPairedSource
public import ComparisonSignedCavityProjectionRestrictionReplacement

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeFreshObservedShape {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (s : T.Slot) (star : ℕ) (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) :
    ActualNaturalBoundaryShape n a p.tree :=
  (G.retainOnMarked 0 (nativeFreshAtSlot T 0 s star) (nativeFreshAtSlot_mem T 0 s star)).retainOnMarked 0 p hp

def nativeFreshObservedReplacementSlots {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (s : T.Slot) (star : ℕ) (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree) : Fin a → p.tree.Slot :=
  nativeMarkedReplacementSlots
    (G.retainOnMarked 0 (nativeFreshAtSlot T 0 s star) (nativeFreshAtSlot_mem T 0 s star))
    ((nativeFreshAtSlot T 0 s star).embed s) p

theorem native_paired_canonical_source_eq_endpoint_retarget
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (star : ℕ)
    (hfixed : ∀e,G.i e≠s) (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0)
    (hne : ∀e,(nativeFreshObservedShape G s star p hp).i e≠nativeFreshObservedReplacementSlots G s star p e)
    (hlow : ∀e,p.tree.splitIndex ((nativeFreshObservedShape G s star p hp).i e)
      ((nativeFreshObservedShape G s star p hp).j e)=
      p.tree.splitIndex ((nativeFreshObservedShape G s star p hp).i e)
        (nativeFreshObservedReplacementSlots G s star p e))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a → NativeSourceFactorForm) (σ : p.tree.cavityLeft.Assignment) :
    let g:=nativeFreshAtSlot T 0 s star
    let Gp:=nativeFreshObservedShape G s star p hp
    let js:=nativeFreshObservedReplacementSlots G s star p
    nativeRestProjectedPairedTest T s star
      (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
      (G.canonicalMinimumSource M forms).restProduct p σ=
      nativeRestEndpointDifference n p.tree (p.embed g.mark) p.mark (p.embed (g.embed s)) σ*
        ((Gp.canonicalMinimumSource M forms).restProduct σ-
          ((Gp.retarget js hne).canonicalMinimumSource M forms).restProduct σ) := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let GF:=G.retainOnMarked 0 g (nativeFreshAtSlot_mem T 0 s star)
  have Hfixed e : GF.i e≠g.embed s:=
    fun H=>hfixed e ((nativeFreshAtSlot_old_splits T 0 s star).1 H)
  have Hold : ((nativeFreshObservedShape G s star p hp).canonicalMinimumSource M forms).restProduct σ=
      (G.canonicalMinimumSource M forms).restProduct (g.restRestrict (p.restRestrict σ)) := by
    rw [nativeFreshObservedShape,ActualNaturalBoundaryShape.retained_canonical_restProduct,
      ActualNaturalBoundaryShape.retained_canonical_restProduct]
  have Hnew:=GF.marked_retarget_canonical_restProduct (g.embed s) Hfixed p 0 hp hne hlow M forms σ
  rw [ActualNaturalBoundaryShape.retained_canonical_restProduct,
    g.restRestrict_replace_target (nativeFreshAtSlot_old_splits T 0 s star).1] at Hnew
  change (((nativeFreshObservedShape G s star p hp).retarget
    (nativeFreshObservedReplacementSlots G s star p) hne).canonicalMinimumSource M forms).restProduct σ = _ at Hnew
  rw [Hold,Hnew]
  unfold nativeRestProjectedPairedTest nativeRestEndpointDifference
  dsimp only
  congr 1
  simp only [MarkedPlacement.restSpin,MarkedPlacement.restRestrict_at]
  simp only [deletedOverlap,mul_comm]

end OAI.SKFluctuations.Cavity
