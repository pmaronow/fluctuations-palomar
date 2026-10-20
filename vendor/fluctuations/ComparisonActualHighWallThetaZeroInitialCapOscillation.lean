module

public import ComparisonActualHighWallThetaZeroInitialCapPoint
public import ComparisonActualHighWallThetaZeroCapComponents

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  {Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
  {P:Q.Potential} (c:ShiftedCapInterval Q P)

theorem initial_radiusS_increment
    (hleft:c.left=Q.data.rmin)
    (hright:P.H c.right=0 ∨ c.right=1)
    {s t:ℝ} (hs:s∈Ioo c.left c.right)
    (ht:t∈Ioo c.left c.right):
    Q.radiusS t-Q.radiusS s≤Q.data.rmin+(c.right-c.left) := by
  have hsi:s∈Icc Q.data.rmin 1:=⟨hleft ▸ hs.1.le,hs.2.le.trans c.hright⟩
  have hti:t∈Icc Q.data.rmin 1:=⟨hleft ▸ ht.1.le,ht.2.le.trans c.hright⟩
  have hS0:0≤Q.radiusS s:=(Q.radius_moments.2.2 s hsi).1.1
  have hSt:Q.radiusS t≤c.right:=by
    rcases hright with hc|hz
    · exact P.cap_point_mean_le_right c.hleft c.hright ht hc (c.negative t ht)
    · rw [hz]
      exact (Q.radius_moments.2.2 t hti).1.2
  rw [hleft]
  linarith

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
