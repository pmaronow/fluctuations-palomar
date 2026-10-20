module

public import ComparisonActualGeneralCMarkedCanonicalSource
public import ComparisonSignedCavityGProjectedRestorationSource

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem physical_canonical_G_projected_displacement_source
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    (bf hf : ℝ→ℝ≥0)
    (forms : Fin a → NativeSourceFactorForm) (s : T.Slot) (star : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (S : ℕ → ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    let GP:=(G.nativeCMarkedLift g (nativeFreshAtSlot_mem T 0 s star)).nativeCMarkedLift p hp
    nativeRestProjectedDisplacementTest T s star
      (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
      (G.canonicalPhysicalSource bf hf forms).restProduct p=
      fun σ=>
        (GP.canonicalPhysicalSource bf hf forms).restProduct σ*
          (deletedOverlap n (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot p.mark),false))
            (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed g.mark)),false))-S star)-
        (GP.canonicalPhysicalSource bf hf forms).restProduct σ*
          (deletedOverlap n (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed (g.embed s))),false))
            (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed g.mark)),false))-S star) := by
  dsimp only
  funext σ
  rw [ActualNaturalBoundaryShape.physicalCMarkedLift_canonical_restProduct,
    ActualNaturalBoundaryShape.physicalCMarkedLift_canonical_restProduct]
  unfold nativeRestProjectedDisplacementTest MarkedPlacement.restSpin
  dsimp only
  rw [(nativeFreshAtSlot T 0 s star).restRestrict_at,p.restRestrict_at,p.restRestrict_at]
  ring

end OAI.SKFluctuations.Cavity
