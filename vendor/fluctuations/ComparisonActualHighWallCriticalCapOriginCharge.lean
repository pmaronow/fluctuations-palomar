module

public import ComparisonActualHighWallAllCapMismatch
public import ComparisonActualHighWallCapOscillation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 8000000
namespace ActualHighWallOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential} (cap : ShiftedCapInterval a P)

theorem critical_initial_cap_mean_le
    (hleft : cap.left=a.data.rmin) (hright : P.H cap.right=0 ∨ cap.right=1)
    {r : ℝ} (hr : r∈Ioo cap.left cap.right) :
    a.radiusS r ≤ a.data.rmin+a.cavityCapTravel := by
  have hSr : a.radiusS r ≤ cap.right := by
    rcases hright with hc|he
    · exact P.full_cap_point_mean_le_right cap.hleft cap.hright hr hc (cap.negative r hr)
    · rw [he]
      exact (a.radius_moments.2.2 r ⟨cap.hleft.trans hr.1.le,hr.2.le.trans cap.hright⟩).1.2
  have ht := cap.travel
  rw [hleft] at ht
  linarith only [hSr,ht]

theorem critical_radiusS_increment_with_origin
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (hleft : P.H cap.left=0 ∨ cap.left=a.data.rmin)
    (hright : P.H cap.right=0 ∨ cap.right=1)
    {s t : ℝ} (hs : s∈Ioo cap.left cap.right) (ht : t∈Ioo cap.left cap.right)
    (hst : s≤t) :
    a.radiusS t-a.radiusS s ≤ 9*Real.log a.data.N*(cap.right-cap.left+a.data.rmin) := by
  have hw : 0≤cap.right-cap.left := sub_nonneg.mpr cap.hlt.le
  have hr0 := a.data.hrbounds.1.le
  have hcoef : 1≤9*Real.log a.data.N := by linarith only [hlog]
  rcases hleft with hc|he
  · have H := cap.radiusS_increment hN hlog hnd hc hright hs ht hst
    exact H.trans (mul_le_mul_of_nonneg_left (by linarith only [hr0]) (by linarith only [hlog]))
  · have hS : a.radiusS t ≤ cap.right := by
      rcases hright with hc|hz
      · exact P.full_cap_point_mean_le_right cap.hleft cap.hright ht hc (cap.negative t ht)
      · rw [hz]
        exact (a.radius_moments.2.2 t ⟨cap.hleft.trans ht.1.le,ht.2.le.trans cap.hright⟩).1.2
    have hS0 : 0≤a.radiusS s :=
      (a.radius_moments.2.2 s ⟨cap.hleft.trans hs.1.le,hs.2.le.trans cap.hright⟩).1.1
    have hp : 0≤cap.right := a.data.hrbounds.1.le.trans (cap.hleft.trans cap.hlt.le)
    have H := mul_le_mul_of_nonneg_right hcoef hp
    rw [one_mul] at H
    rw [he]
    nlinarith only [hS,hS0,H]

end ActualHighWallOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
