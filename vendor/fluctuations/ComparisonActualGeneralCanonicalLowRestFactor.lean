module

public import ComparisonActualGeneralCanonicalMarkedReset
public import ComparisonSignedCavityCanonicalOldLowMoment

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 15000000
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def canonicalPhysicalLowRestFactor (bf hf : ℝ→ℝ≥0)
    (i j : T.Slot) (σ : T.cavityLeft.Assignment) : ℝ :=
  let u:=partitionPoint 0 as (T.splitIndex i j)
  fullBoundaryAffineFactor n (hf u) (bf u)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot j),false)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot i),false)

theorem canonical_physical_cons_restProduct (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (i j : T.Slot) (hij : i≠j) (σ : T.cavityLeft.Assignment) :
    ((G.consLowShape i j hij).canonicalPhysicalSource bf hf (Fin.cases .row f)).restProduct σ=
      canonicalPhysicalLowRestFactor bf hf i j σ*(G.canonicalPhysicalSource bf hf f).restProduct σ := by
  unfold restProduct
  rw [Fin.prod_univ_succ]
  rfl

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
