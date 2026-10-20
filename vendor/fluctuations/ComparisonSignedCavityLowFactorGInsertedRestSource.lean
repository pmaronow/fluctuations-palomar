module

public import ComparisonSignedCavityLowFactorGMarkedSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem ActualNaturalBoundaryShape.native_inserted_canonical_low_rest_test
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (U : ℕ) (b S : ℕ→ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hlow : r.tree.splitIndex (r.embed p.mark) r.mark<U) :
    insertedRestTest (G.canonicalMinimumSource M forms).restProduct (restCenteredLowKernel n U b S) p r=
      fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalMinimumSource M forms).restProduct σ*
        (b (r.tree.splitIndex (r.embed p.mark) r.mark)*(deletedOverlap n
          (joinSpin (r.tree.cavityLeft.atSlot σ (r.tree.cavityLeftSlot (r.embed p.mark)),false))
          (joinSpin (r.tree.cavityLeft.atSlot σ (r.tree.cavityLeftSlot r.mark),false))-
          S (r.tree.splitIndex (r.embed p.mark) r.mark))) := by
  funext σ
  rw [ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct,
    ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct]
  simp only [insertedRestTest,restCenteredLowKernel,hlow,ite_true,
    MarkedPlacement.restSpin,r.restRestrict_at]
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
