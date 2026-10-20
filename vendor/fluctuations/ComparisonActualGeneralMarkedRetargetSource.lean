module

public import ComparisonActualGeneralRetargetSource
public import ComparisonActualGeneralCanonicalMarkedReset
public import ComparisonSignedCavityGeneratedPairedRetargetShape

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators

theorem ActualNaturalBoundaryShape.marked_retarget_canonical_physical_restProduct
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot)
    (hfixed : ∀e,G.i e≠s) (p : MarkedPlacement T) (r : ℝ) (hp : p∈T.markedAttach r)
    (hne : ∀e,(G.retainOnMarked r p hp).i e≠nativeMarkedReplacementSlots G s p e)
    (hlow : ∀e,p.tree.splitIndex ((G.retainOnMarked r p hp).i e)
      ((G.retainOnMarked r p hp).j e)=p.tree.splitIndex ((G.retainOnMarked r p hp).i e)
        (nativeMarkedReplacementSlots G s p e))
    (bf hf : ℝ→ℝ≥0)
    (f : Fin a → NativeSourceFactorForm) (σ : p.tree.cavityLeft.Assignment) :
    (((G.retainOnMarked r p hp).retarget (nativeMarkedReplacementSlots G s p) hne).canonicalPhysicalSource bf hf f).restProduct σ=
      (G.canonicalPhysicalSource bf hf f).restProduct
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot s) (p.restRestrict σ) (p.restSpin σ)) := by
  rw [(G.retainOnMarked r p hp).retarget_canonicalPhysicalSource bf hf f _ hne hlow]
  have H:=(G.canonicalPhysicalSource bf hf f).marked_retarget_restProduct s hfixed p r hp hne σ
  simpa only [restProduct,retarget,canonicalPhysicalSource,retainOnMarked,sourceLowMass,nativeMarkedReplacementSlots,
    (T.markedAttach_embed_preserves r p hp).2] using H

end OAI.SKFluctuations.Cavity
