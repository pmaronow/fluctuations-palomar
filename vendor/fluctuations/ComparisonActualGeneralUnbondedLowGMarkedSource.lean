module

public import ComparisonActualGeneralCMarkedCanonicalSource
public import ComparisonSignedCavityUnbondedLowGMarkedSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem ActualNaturalBoundaryShape.physical_double_marked_unbonded_low_pair_test
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    (bf hf : ℝ→ℝ≥0)
    (forms : Fin a→NativeSourceFactorForm) (S : ℕ→ℝ) (u z : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
    (fun σ=>(G.canonicalPhysicalSource bf hf forms).restProduct
        (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
      (deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot u),false))
        (joinSpin (T.cavityLeft.atSlot (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)) (T.cavityLeftSlot z),false))-
          S (T.splitIndex u z)))=
    fun σ=>(((G.nativeCMarkedLift p hp).nativeCMarkedLift r hr).canonicalPhysicalSource bf hf forms).product σ*
      (deletedOverlap n (joinSpin (r.tree.atSlot σ (r.embed (p.embed u))))
          (joinSpin (r.tree.atSlot σ (r.embed (p.embed z))))-
          S (r.tree.splitIndex (r.embed (p.embed u)) (r.embed (p.embed z)))) := by
  funext σ
  rw [G.physicalCDoubleMarkedLift_canonical_product bf hf forms p hp r hr]
  rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
  simp only [p.restRestrict_at,r.restRestrict_at,r.tree.atSlot_cavityLeft]
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
