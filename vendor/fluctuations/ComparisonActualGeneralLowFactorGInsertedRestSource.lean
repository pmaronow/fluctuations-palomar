module

public import ComparisonActualGeneralCMarkedCanonicalSource
public import ComparisonSignedCavityLowFactorGInsertedRestSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem ActualNaturalBoundaryShape.physical_inserted_canonical_low_rest_test
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    (bf hf : ℝ→ℝ≥0)
    (forms : Fin a→NativeSourceFactorForm) (U : ℕ) (b S : ℕ→ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hlow : r.tree.splitIndex (r.embed p.mark) r.mark<U) :
    insertedRestTest (G.canonicalPhysicalSource bf hf forms).restProduct (restCenteredLowKernel n U b S) p r=
      fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalPhysicalSource bf hf forms).restProduct σ*
        (b (r.tree.splitIndex (r.embed p.mark) r.mark)*(deletedOverlap n
          (joinSpin (r.tree.cavityLeft.atSlot σ (r.tree.cavityLeftSlot (r.embed p.mark)),false))
          (joinSpin (r.tree.cavityLeft.atSlot σ (r.tree.cavityLeftSlot r.mark),false))-
          S (r.tree.splitIndex (r.embed p.mark) r.mark))) := by
  funext σ
  rw [ActualNaturalBoundaryShape.physicalCMarkedLift_canonical_restProduct,
    ActualNaturalBoundaryShape.physicalCMarkedLift_canonical_restProduct]
  simp only [insertedRestTest,restCenteredLowKernel,hlow,ite_true,
    MarkedPlacement.restSpin,r.restRestrict_at]
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
