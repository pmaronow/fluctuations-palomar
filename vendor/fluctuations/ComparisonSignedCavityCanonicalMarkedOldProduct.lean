module

public import ComparisonSignedCavityCanonicalOldLowMoment
public import ComparisonSignedCavityForestObservedHighGeometry
public import ComparisonSignedCavityOriginalFreshMomentBound

@[expose] public section

noncomputable section
set_option maxHeartbeats 6500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def retainOnMarked (G : ActualNaturalBoundaryShape n a T) (r : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach r) : ActualNaturalBoundaryShape n a p.tree where
  α:=G.α
  β:=G.β
  i:=fun e=>p.embed (G.i e)
  j:=fun e=>p.embed (G.j e)
  distinct:=fun e h=>G.distinct e ((T.markedAttach_embed_preserves r p hp).1 h)
  lowInGrid:=by
    intro e
    rw [(T.markedAttach_embed_preserves r p hp).2]
    exact G.lowInGrid e

theorem retained_source_mass (G : ActualNaturalBoundaryShape n a T) (r : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach r) (e : Fin a) :
    (G.retainOnMarked r p hp).sourceLowMass e=G.sourceLowMass e := by
  unfold sourceLowMass retainOnMarked
  rw [(T.markedAttach_embed_preserves r p hp).2]

theorem retained_restProduct (G : ActualNaturalBoundaryShape n a T) (r : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach r) (σ : p.tree.cavityLeft.Assignment) :
    (G.retainOnMarked r p hp).restProduct σ=G.restProduct (p.restRestrict σ) := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [retainOnMarked,p.restRestrict_at]

theorem retained_canonical_restProduct {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm) (r : ℝ)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach r) (σ : p.tree.cavityLeft.Assignment) :
    ((G.retainOnMarked r p hp).canonicalMinimumSource M f).restProduct σ=
      (G.canonicalMinimumSource M f).restProduct (p.restRestrict σ) := by
  rw [←(G.canonicalMinimumSource M f).retained_restProduct r p hp σ]
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalMinimumSource,retainOnMarked,sourceLowMass,
    (T.markedAttach_embed_preserves r p hp).2]

end ActualNaturalBoundaryShape

theorem nativeOriginalFreshResidual_same_zero (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s b : T.Slot) (a : ℝ) (star : ℕ)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (Z : T.cavityLeft.Assignment→ℝ) :
    nativeOriginalFreshResidual n T s s b a star v q x Z=0 := by
  simp [nativeOriginalFreshResidual,ClockTree.disorderExpect]

end OAI.SKFluctuations.Cavity
