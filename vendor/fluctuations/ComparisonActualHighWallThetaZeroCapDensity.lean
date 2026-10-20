module

public import ComparisonActualHighWallThetaZeroSelectedRadius
public import ComparisonCapIntervals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

def cavityCapTravel:ℝ:=
  (comparisonConstraintLength Q.data.N Q.data.E Q.data.d/Q.data.N^delta)*
    Real.log ((1+comparisonSmallMass Q.data.N Q.data.E)/
      comparisonSmallMass Q.data.N Q.data.E)

theorem Potential.cap_density_on_interval (P:Q.Potential)
    {l r:ℝ} (hl:Q.data.rmin≤l) (hr:r≤1)
    (hnegative:∀t∈Ioo l r,P.H t<0):
    ∀ᵐt,t∈Icc l r→deriv Q.alpha.val.val t=Q.data.M (Q.alpha.val.val t):=by
  filter_upwards [P.hbang,volume.ae_ne l,volume.ae_ne r] with t ht htl htr hti
  exact ht ⟨hl.trans hti.1,hti.2.trans hr⟩
    (hnegative t ⟨lt_of_le_of_ne hti.1 htl.symm,
      lt_of_le_of_ne hti.2 htr⟩)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
