module

public import ComparisonSignedCavityCanonicalSourceMoments
public import ComparisonSignedCavityActualTerminalGAtom

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def ActualNaturalBoundaryShape.onMarked {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) : ActualNaturalBoundaryShape n a p.tree where
  α:=G.α
  β:=G.β
  i:=fun e=>p.embed (G.i e)
  j:=fun e=>p.embed (G.j e)
  distinct:=fun e h=>G.distinct e ((T.markedAttach_embed_preserves 0 p hp).1 h)
  lowInGrid:=fun _=>p.tree.splitIndex_le_clockLength _ _

theorem ActualNaturalBoundaryShape.onMarked_sourceLowMass {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) (e : Fin a) :
    (G.onMarked p hp).sourceLowMass e=G.sourceLowMass e := by
  unfold ActualNaturalBoundaryShape.sourceLowMass ActualNaturalBoundaryShape.onMarked
  rw [(T.markedAttach_embed_preserves 0 p hp).2]

theorem ActualNaturalBoundaryShape.onMarked_canonical_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : p.tree.Assignment) :
    ((G.onMarked p hp).canonicalMinimumSource M forms).product σ=
      (G.canonicalMinimumSource M forms).product (p.restrict σ) := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [ActualNaturalBoundaryShape.canonicalMinimumSource]
  rw [G.onMarked_sourceLowMass p hp e]
  simp only [ActualNaturalBoundaryShape.onMarked,p.restrict_at]

def NativeOriginalGMarkedWord.canonicalOldShape {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    (G : ActualNaturalBoundaryShape n a T) : ActualNaturalBoundaryShape n a g.tree:=
  ((G.onMarked g.p g.hp).onMarked g.r g.hr).onMarked g.z g.hz

theorem NativeOriginalGMarkedWord.canonicalOldShape_sourceLowMass {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T)
    (G : ActualNaturalBoundaryShape n a T) (e : Fin a) :
    (g.canonicalOldShape G).sourceLowMass e=G.sourceLowMass e := by
  dsimp only [NativeOriginalGMarkedWord.canonicalOldShape]
  exact (((G.onMarked g.p g.hp).onMarked g.r g.hr).onMarked_sourceLowMass g.z g.hz e).trans
    (((G.onMarked g.p g.hp).onMarked_sourceLowMass g.r g.hr e).trans
      (G.onMarked_sourceLowMass g.p g.hp e))

theorem NativeOriginalGMarkedWord.canonicalOldShape_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : g.tree.Assignment) :
    ((g.canonicalOldShape G).canonicalMinimumSource M forms).product σ=
      (G.canonicalMinimumSource M forms).product (g.p.restrict (g.r.restrict (g.z.restrict σ))) := by
  dsimp only [NativeOriginalGMarkedWord.canonicalOldShape]
  exact (((G.onMarked g.p g.hp).onMarked g.r g.hr).onMarked_canonical_product g.z g.hz M forms σ).trans
    (((G.onMarked g.p g.hp).onMarked_canonical_product g.r g.hr M forms (g.z.restrict σ)).trans
      (G.onMarked_canonical_product g.p g.hp M forms (g.r.restrict (g.z.restrict σ))))

theorem NativeOriginalGMarkedWord.leaves_le {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (g : NativeOriginalGMarkedWord T) : g.tree.leaves ≤ T.leaves+3 := by
  have H1:=T.markedAttach_leaves 0 g.p g.hp
  have H2:=g.p.tree.markedAttach_leaves 0 g.r g.hr
  have H3:=g.r.tree.markedAttach_leaves 0 g.z g.hz
  dsimp only [NativeOriginalGMarkedWord.tree]
  omega

end OAI.SKFluctuations.Cavity
