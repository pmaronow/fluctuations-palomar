module

public import ComparisonSignedCavityCanonicalTwoHighLowBudget
public import ComparisonSignedCavityCanonicalRestMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def nativeCMarkedLift (G : ActualNaturalBoundaryShape n a T)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) : ActualNaturalBoundaryShape n a p.tree where
  α:=G.α
  β:=G.β
  i:=fun e=>p.embed (G.i e)
  j:=fun e=>p.embed (G.j e)
  distinct:=fun e h=>G.distinct e ((T.markedAttach_embed_preserves 0 p hp).1 h)
  lowInGrid:=by
    intro e
    rw [(T.markedAttach_embed_preserves 0 p hp).2]
    exact G.lowInGrid e

theorem nativeCMarkedLift_sourceLowMass (G : ActualNaturalBoundaryShape n a T)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (e : Fin a) :
    (G.nativeCMarkedLift p hp).sourceLowMass e=G.sourceLowMass e := by
  dsimp only [sourceLowMass,nativeCMarkedLift]
  rw [(T.markedAttach_embed_preserves 0 p hp).2]

theorem nativeCMarkedLift_restProduct (G : ActualNaturalBoundaryShape n a T)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (σ : p.tree.cavityLeft.Assignment) :
    (G.nativeCMarkedLift p hp).restProduct σ=G.restProduct (p.restRestrict σ) := by
  unfold restProduct
  simp only [nativeCMarkedLift]
  simp_rw [p.restRestrict_at]

theorem nativeCMarkedLift_canonical_restProduct
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (σ : p.tree.cavityLeft.Assignment) :
    ((G.nativeCMarkedLift p hp).canonicalMinimumSource M f).restProduct σ=
      (G.canonicalMinimumSource M f).restProduct (p.restRestrict σ) := by
  simp only [restProduct,canonicalMinimumSource,nativeCMarkedLift,sourceLowMass,
    (T.markedAttach_embed_preserves 0 p hp).2,p.restRestrict_at]

theorem nativeCMarkedLift_canonical_product
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) (σ : p.tree.Assignment) :
    ((G.nativeCMarkedLift p hp).canonicalMinimumSource M f).product σ=
      (G.canonicalMinimumSource M f).restProduct (p.restRestrict (p.tree.cavityAssignment σ).1) := by
  rw [product_eq_restProduct,nativeCMarkedLift_canonical_restProduct]

theorem nativeCDoubleMarkedLift_canonical_product
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) (σ : r.tree.Assignment) :
    (((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalMinimumSource M f).product σ=
      (G.canonicalMinimumSource M f).restProduct
        (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) := by
  rw [nativeCMarkedLift_canonical_product,nativeCMarkedLift_canonical_restProduct]

theorem nativeC_inserted_canonical_low_test
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (U : ℕ) (b S : ℕ→ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hlow : r.tree.splitIndex (r.embed p.mark) r.mark < U) :
    (fun σ=>insertedRestTest (G.canonicalMinimumSource M f).restProduct
      (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1)=
      fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalMinimumSource M f).product σ*
        (b (r.tree.splitIndex (r.embed p.mark) r.mark)*
          (deletedOverlap n (joinSpin (r.tree.atSlot σ (r.embed p.mark)))
            (joinSpin (r.tree.atSlot σ r.mark))-S (r.tree.splitIndex (r.embed p.mark) r.mark))) := by
  funext σ
  rw [nativeCDoubleMarkedLift_canonical_product]
  simp only [insertedRestTest,restCenteredLowKernel,hlow,ite_true,
    ClockTree.MarkedPlacement.restSpin,r.restRestrict_at,r.tree.atSlot_cavityLeft]
  simp [deletedOverlap,joinSpin]

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
