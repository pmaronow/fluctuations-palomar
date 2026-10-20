module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

def Eq7InnerBroadFourPerScale {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P) : Prop :=
  ∀ v : ℝ, 0 < v → Q.data.s ≤ v →
    (Finset.univ.filter (fun p : Eq7InnerBroadSliceIndex c =>
      (eq7InnerBroadSampler c p.1).scale p.2 = v)).card ≤ 4

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
