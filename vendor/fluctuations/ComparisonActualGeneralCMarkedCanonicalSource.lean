module

public import ComparisonActualGeneralMarkedSourceTransport
public import ComparisonSignedCavityOriginalCMarkedCanonicalSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem physicalCMarkedLift_canonical_restProduct
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (σ : p.tree.cavityLeft.Assignment) :
    ((G.nativeCMarkedLift p hp).canonicalPhysicalSource bf hf f).restProduct σ=
      (G.canonicalPhysicalSource bf hf f).restProduct (p.restRestrict σ) := by
  simp only [restProduct,canonicalPhysicalSource,nativeCMarkedLift,sourceLowMass,
    (T.markedAttach_embed_preserves 0 p hp).2,p.restRestrict_at]

theorem physicalCMarkedLift_canonical_product
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (σ : p.tree.Assignment) :
    ((G.nativeCMarkedLift p hp).canonicalPhysicalSource bf hf f).product σ=
      (G.canonicalPhysicalSource bf hf f).restProduct (p.restRestrict (p.tree.cavityAssignment σ).1) := by
  rw [product_eq_restProduct,physicalCMarkedLift_canonical_restProduct]

theorem physicalCDoubleMarkedLift_canonical_product
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) (σ : r.tree.Assignment) :
    (((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalPhysicalSource bf hf f).product σ=
      (G.canonicalPhysicalSource bf hf f).restProduct
        (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) := by
  rw [physicalCMarkedLift_canonical_product,physicalCMarkedLift_canonical_restProduct]

theorem physicalC_inserted_canonical_low_test
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (U : ℕ) (b S : ℕ→ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hlow : r.tree.splitIndex (r.embed p.mark) r.mark < U) :
    (fun σ=>insertedRestTest (G.canonicalPhysicalSource bf hf f).restProduct
      (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1)=
      fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalPhysicalSource bf hf f).product σ*
        (b (r.tree.splitIndex (r.embed p.mark) r.mark)*
          (deletedOverlap n (joinSpin (r.tree.atSlot σ (r.embed p.mark)))
            (joinSpin (r.tree.atSlot σ r.mark))-S (r.tree.splitIndex (r.embed p.mark) r.mark))) := by
  funext σ
  rw [physicalCDoubleMarkedLift_canonical_product]
  simp only [insertedRestTest,restCenteredLowKernel,hlow,ite_true,
    ClockTree.MarkedPlacement.restSpin,r.restRestrict_at,r.tree.atSlot_cavityLeft]
  simp [deletedOverlap,joinSpin]

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
