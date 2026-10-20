module

public import ComparisonSignedCavityInitialInsertionWordLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree.NativeInitialInsertionWord
open OAI.SKFluctuations.Cavity OAI.SKFluctuations.Hierarchy OAI.SKFluctuations.LaplaceWindowFormalization
set_option maxHeartbeats 24000000

variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {k : ℕ}

 def canonicalShape (g : ClockTree.NativeInitialInsertionWord T k)
    (G : ActualNaturalBoundaryShape n a T) : ActualNaturalBoundaryShape n a g.tree := by
  induction g with
  | done T=>exact G
  | pair p hp r hr tail ih=>exact ih ((G.onMarked p hp).onMarked r hr)

 theorem canonicalShape_sourceLowMass (g : ClockTree.NativeInitialInsertionWord T k)
    (G : ActualNaturalBoundaryShape n a T) (e : Fin a) :
    (g.canonicalShape G).sourceLowMass e=G.sourceLowMass e := by
  induction g with
  | done T=>rfl
  | pair p hp r hr tail ih=>
    exact (ih _).trans (((G.onMarked p hp).onMarked_sourceLowMass r hr e).trans (G.onMarked_sourceLowMass p hp e))

 theorem canonicalShape_product (g : ClockTree.NativeInitialInsertionWord T k)
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : g.tree.Assignment) :
    ((g.canonicalShape G).canonicalMinimumSource M forms).product σ=
      (G.canonicalMinimumSource M forms).product (g.restrict σ) := by
  induction g with
  | done T=>rfl
  | pair p hp r hr tail ih=>
    dsimp only [tree] at σ
    change ((tail.canonicalShape ((G.onMarked p hp).onMarked r hr)).canonicalMinimumSource M forms).product σ=
      (G.canonicalMinimumSource M forms).product (p.restrict (r.restrict (tail.restrict σ)))
    rw [ih]
    rw [(G.onMarked p hp).onMarked_canonical_product r hr M forms,
      G.onMarked_canonical_product p hp M forms]

end OAI.SKFluctuations.Hierarchy.ClockTree.NativeInitialInsertionWord
