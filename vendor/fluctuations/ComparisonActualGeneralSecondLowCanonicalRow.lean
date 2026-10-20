module

public import ComparisonActualGeneralCanonicalLowRestFactor
public import ComparisonSignedCavitySecondLowUnweightedCMarkedCanonicalSource

@[expose] public section
noncomputable section
set_option maxHeartbeats 15000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
 theorem physical_unweighted_c_canonical_row_eq_LOW
    (n U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (bf hf : ℝ→ℝ≥0)
    (f c : T.Slot) (hlow : T.splitIndex f c<U) (τ : T.cavityLeft.Assignment) :
    ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor bf hf f c τ=
      restLowKernel n U (fun j=>(bf (partitionPoint 0 as j):ℝ))
        (fun j=>(hf (partitionPoint 0 as j):ℝ)) (T.splitIndex f c)
        (T.cavityLeft.atSlot τ (T.cavityLeftSlot f)) (T.cavityLeft.atSlot τ (T.cavityLeftSlot c)) := by
  simp only [ActualNaturalBoundaryShape.canonicalPhysicalLowRestFactor,fullBoundaryAffineFactor,
    restLowKernel,hlow,ite_true,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end OAI.SKFluctuations.Cavity
