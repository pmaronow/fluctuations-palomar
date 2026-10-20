module

public import ComparisonSignedCavitySecondLowOccupiedOldCanonicalOrientation
public import ComparisonActualGeneralCanonicalMarkedReset

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
theorem orientAway_physical_restProduct
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ)
    (forms : Fin a→NativeSourceFactorForm) (σ : T.cavityLeft.Assignment) :
    ((G.orientAway s U).canonicalPhysicalSource bf hf forms).restProduct σ=
      (G.canonicalPhysicalSource bf hf forms).restProduct σ := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalPhysicalSource,G.orientAway_sourceLowMass]
  dsimp only [orientAway]
  split_ifs
  · exact fullBoundaryAffineFactor_swap n _ _ _ _
  · rfl

end ActualNaturalBoundaryShape
theorem actual_general_second_low_fresh_observed_oriented_complete_rest_source
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (star U : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (c : p.tree.Slot)
    (bf hf : ℝ→ℝ≥0)
    (forms : Fin a→NativeSourceFactorForm) (σ : p.tree.cavityLeft.Assignment) :
    (((nativeFreshObservedShape G s star p hp).orientAway c U).canonicalPhysicalSource bf hf forms).restProduct σ=
      (G.canonicalPhysicalSource bf hf forms).restProduct
        ((nativeFreshAtSlot T 0 s star).restRestrict (p.restRestrict σ)) := by
  rw [ActualNaturalBoundaryShape.orientAway_physical_restProduct,nativeFreshObservedShape,
    ActualNaturalBoundaryShape.retained_canonical_physical_restProduct,
    ActualNaturalBoundaryShape.retained_canonical_physical_restProduct]

end OAI.SKFluctuations.Cavity
