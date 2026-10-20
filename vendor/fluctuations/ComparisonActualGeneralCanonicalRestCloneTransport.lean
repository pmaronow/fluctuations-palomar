module

public import ComparisonActualGeneralCanonicalMarkedReset
public import ComparisonSignedCavityCanonicalRestCloneTransport

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 15000000
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem onCloneOld_physical_restProduct
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (target : T.Slot) (cut : ℕ)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    ((G.onCloneOld target cut).canonicalPhysicalSource bf hf forms).restProduct σ=
      (G.canonicalPhysicalSource bf hf forms).restProduct
        ((nativeCloneBlockAtSlot T target cut).restOldRestrict σ) := by
  rw [←(G.canonicalPhysicalSource bf hf forms).onCloneOld_restProduct target cut σ]
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalPhysicalSource,onCloneOld,sourceLowMass,
    (nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]

theorem onCloneOld_retarget_new_physical_restProduct
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (target : T.Slot) (cut : ℕ) (hout : ∀e,T.splitIndex target (G.i e)<cut)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    (((G.onCloneOld target cut).retarget
      (fun e=>(nativeCloneBlockAtSlot T target cut).newEmbed (G.j e))
      (G.clone_new_targets_ne target cut hout)).canonicalPhysicalSource bf hf forms).restProduct σ=
      (G.canonicalPhysicalSource bf hf forms).restProduct
        ((nativeCloneBlockAtSlot T target cut).restNewRestrict σ) := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  have Hlow:=G.clone_new_targets_same_low target cut hout e
  have hanchor:=nativeCloneBlockAtSlot_exterior_shared T target cut (G.i e) (hout e)
  simp only [canonicalPhysicalSource,ActualNaturalBoundaryShape.retarget,onCloneOld,
    sourceLowMass] at Hlow ⊢
  rw [←Hlow,(nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]
  rw [NativeRetainedSubtreeClone.restNewRestrict_at,NativeRetainedSubtreeClone.restNewRestrict_at]
  rw [hanchor]

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
