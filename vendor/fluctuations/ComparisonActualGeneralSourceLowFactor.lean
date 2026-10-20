module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityCanonicalUnbondedLowFactor

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem physical_source_prepend_bond_product {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (bf hf : ℝ→ℝ≥0)
    (f : Fin a→NativeSourceFactorForm) (c d : T.Slot) (hcd : c≠d) (σ : T.Assignment) :
    ((G.prependSourceEdge c d hcd).canonicalPhysicalSource bf hf (Fin.cases .bondCentered f)).product σ=
      (bf (partitionPoint 0 as (T.splitIndex c d)):ℝ)*
        (deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d))-
          pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
            (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
            (partitionPoint 0 as (T.splitIndex c d)))*(G.canonicalPhysicalSource bf hf f).product σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_succ]
  simp only [ActualNaturalBoundaryShape.canonicalPhysicalSource,
    ActualNaturalBoundaryShape.prependSourceEdge,ActualNaturalBoundaryShape.sourceLowMass,
    Fin.cases_zero,Fin.cases_succ,NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope]
  congr 1
  unfold fullBoundaryAffineFactor
  have HE : deletedOverlap n (joinSpin (T.atSlot σ d)) (joinSpin (T.atSlot σ c))=
      deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d)) := by
    simp only [deletedOverlap,mul_comm]
  rw [HE]
  ring

theorem physical_source_prepend_centered_product {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (bf hf : ℝ→ℝ≥0)
    (f : Fin a→NativeSourceFactorForm) (c d : T.Slot) (hcd : c≠d) (σ : T.Assignment) :
    ((G.prependSourceEdge c d hcd).canonicalPhysicalSource bf hf (Fin.cases .centered f)).product σ=
      (deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d))-
          pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
            (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
            (partitionPoint 0 as (T.splitIndex c d)))*(G.canonicalPhysicalSource bf hf f).product σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_succ]
  simp only [ActualNaturalBoundaryShape.canonicalPhysicalSource,
    ActualNaturalBoundaryShape.prependSourceEdge,ActualNaturalBoundaryShape.sourceLowMass,
    Fin.cases_zero,Fin.cases_succ,NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope]
  congr 1
  unfold fullBoundaryAffineFactor
  have HE : deletedOverlap n (joinSpin (T.atSlot σ d)) (joinSpin (T.atSlot σ c))=
      deletedOverlap n (joinSpin (T.atSlot σ c)) (joinSpin (T.atSlot σ d)) := by
    simp only [deletedOverlap,mul_comm]
  rw [HE]
  ring

end OAI.SKFluctuations.Cavity
