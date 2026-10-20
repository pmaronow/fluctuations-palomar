module

public import ComparisonActualHighWallCanonicalRestMoments
public import ComparisonSignedCavityCanonicalOldLowMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def actualHighWallLowRestFactor {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (i j : T.Slot) (σ : T.cavityLeft.Assignment) : ℝ :=
  let u:=partitionPoint 0 as (T.splitIndex i j)
  fullBoundaryAffineFactor n (M.hf u) (M.bf u)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot j),false)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot i),false)

theorem actual_high_wall_canonical_cons_restProduct {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (i j : T.Slot) (hij : i≠j) (σ : T.cavityLeft.Assignment) :
    ((G.consLowShape i j hij).canonicalHighWallSource M (Fin.cases .row f)).restProduct σ=
      actualHighWallLowRestFactor M i j σ*(G.canonicalHighWallSource M f).restProduct σ := by
  unfold restProduct
  rw [Fin.prod_univ_succ]
  rfl

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
