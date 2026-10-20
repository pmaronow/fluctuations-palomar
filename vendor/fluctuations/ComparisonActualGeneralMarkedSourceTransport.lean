module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityGRestorationWords

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem ActualNaturalBoundaryShape.onMarked_physical_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (bf hf : ℝ→ℝ≥0)
    (forms : Fin a→NativeSourceFactorForm) (σ : p.tree.Assignment) :
    ((G.onMarked p hp).canonicalPhysicalSource bf hf forms).product σ=
      (G.canonicalPhysicalSource bf hf forms).product (p.restrict σ) := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [ActualNaturalBoundaryShape.canonicalPhysicalSource]
  rw [G.onMarked_sourceLowMass p hp e]
  simp only [ActualNaturalBoundaryShape.onMarked,p.restrict_at]

theorem NativeOriginalGMarkedWord.canonicalOldShape_physical_product
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (G : ActualNaturalBoundaryShape n a T)
    (bf hf : ℝ→ℝ≥0)
    (forms : Fin a→NativeSourceFactorForm) (σ : g.tree.Assignment) :
    ((g.canonicalOldShape G).canonicalPhysicalSource bf hf forms).product σ=
      (G.canonicalPhysicalSource bf hf forms).product (g.p.restrict (g.r.restrict (g.z.restrict σ))) := by
  dsimp only [NativeOriginalGMarkedWord.canonicalOldShape]
  exact (((G.onMarked g.p g.hp).onMarked g.r g.hr).onMarked_physical_product g.z g.hz bf hf forms σ).trans
    (((G.onMarked g.p g.hp).onMarked_physical_product g.r g.hr bf hf forms (g.z.restrict σ)).trans
      (G.onMarked_physical_product g.p g.hp bf hf forms (g.r.restrict (g.z.restrict σ))))

theorem NativeOriginalGMarkedWord.originalRestorationTest_physical
    {n aDegree : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (G : ActualNaturalBoundaryShape n aDegree T)
    (bf hf : ℝ→ℝ≥0)
    (forms : Fin aDegree→NativeSourceFactorForm) (U : ℕ) (K b S : ℕ→ℝ) (a : T.Slot) :
    g.originalRestorationTest U K b S (G.canonicalPhysicalSource bf hf forms).product a=
      fun σ=>((g.canonicalOldShape G).canonicalPhysicalSource bf hf forms).product σ*
        nativeOriginalHighGAtom g.tree U K b S
          (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
          (g.z.embed g.r.mark) g.z.mark σ := by
  funext σ
  rw [g.canonicalOldShape_physical_product G bf hf forms σ]
  rfl

end OAI.SKFluctuations.Cavity
