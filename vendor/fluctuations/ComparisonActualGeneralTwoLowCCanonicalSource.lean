module

public import ComparisonActualGeneralCanonicalLowRestFactor
public import ComparisonSignedCavitySecondLowUnweightedCCanonicalSource

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 15000000
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

 theorem consTwoLowC_physical_restProduct
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (f c z : T.Slot) (hfc : f≠c) (hzc : z≠c) (τ : T.cavityLeft.Assignment) :
    ((G.consTwoLowC f c z hfc hzc).canonicalPhysicalSource bf hf (twoLowCForms forms)).restProduct τ=
      canonicalPhysicalLowRestFactor bf hf z c τ*canonicalPhysicalLowRestFactor bf hf f c τ*
        (G.canonicalPhysicalSource bf hf forms).restProduct τ := by
  unfold consTwoLowC twoLowCForms
  rw [canonical_physical_cons_restProduct,canonical_physical_cons_restProduct]
  ring

 theorem consTwoLowC_physical_complete_old_difference
    (bf hf : ℝ→ℝ≥0)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (f c z c' : T.Slot) (hfc : f≠c) (hzc : z≠c) (hfc' : f≠c') (hzc' : z≠c')
    (τ : T.cavityLeft.Assignment) :
    ((G.consTwoLowC f c z hfc hzc).canonicalPhysicalSource bf hf (twoLowCForms forms)).restProduct τ-
      ((G.consTwoLowC f c' z hfc' hzc').canonicalPhysicalSource bf hf (twoLowCForms forms)).restProduct τ=
      (G.canonicalPhysicalSource bf hf forms).restProduct τ*
        (canonicalPhysicalLowRestFactor bf hf f c τ*canonicalPhysicalLowRestFactor bf hf z c τ-
          canonicalPhysicalLowRestFactor bf hf f c' τ*canonicalPhysicalLowRestFactor bf hf z c' τ) := by
  rw [consTwoLowC_physical_restProduct,consTwoLowC_physical_restProduct]
  ring

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
