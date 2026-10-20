module

public import ComparisonSignedCavityActualDyadicCutDepth
public import ComparisonActualHighWallBufferEndpointGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy Cavity ActualHighWallOverlapMinimum
open scoped Topology BigOperators
set_option maxHeartbeats 10000000

namespace ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_dyadic_cut_depth_log_bound
    {m delta cl cu Az C0 Ct D Bclock Cx : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,Cx*M.xs ≤ a → a ≤ 1 →
        (nativeDyadicCutDepth a:ℝ) ≤ (2+3/Real.log 2)*Real.log ((n+1:ℕ):ℝ) := by
  have Hlower:=eventually_actual_high_wall_scale_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=Cx) (q:=-(3:ℝ)) (r:=-(2:ℝ)) hCx (by norm_num))
  have HN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hlog:=(Real.tendsto_log_atTop.comp HN).eventually_ge_atTop 1
  filter_upwards [Hlower,Hcoef,Hlog] with n hnLower hnCoef hnLog
  intro M a ha ha1
  have ha0 : 0 < a:=(mul_pos hCx M.hxs).trans_le ha
  have Hpoly : ((n+1:ℕ):ℝ)^(-(3:ℝ)) ≤ a:=by
    apply (show ((n+1:ℕ):ℝ)^(-(3:ℝ)) ≤ Cx*((n+1:ℕ):ℝ)^(-(2:ℝ)) by
      simpa only [one_mul] using hnCoef).trans
    exact (mul_le_mul_of_nonneg_left (hnLower M) hCx.le).trans ha
  exact nativeDyadicCutDepth_le_log_of_polynomial_lower ha0 ha1 (Nat.cast_pos.mpr (by omega : 0<n+1)) hnLog Hpoly

theorem eventually_actual_high_wall_dyadic_cut_depth_power_bound
    {m delta cl cu Az C0 Ct D Bclock Cx eps : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx) (heps : 0 < eps) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,Cx*M.xs ≤ a → a ≤ 1 → (nativeDyadicCutDepth a:ℝ) ≤ ((n+1:ℕ):ℝ)^eps := by
  have Hlog:=eventually_actual_high_wall_dyadic_cut_depth_log_bound
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hCx
  have HN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hloss:=HN.eventually (comparison_log_loss_eventually
    (C:=2+3/Real.log 2) (p:=1) (by have :=Real.log_pos (by norm_num : (1:ℝ) < 2);positivity) heps)
  filter_upwards [Hlog,Hloss] with n hn hLoss
  intro M a ha ha1
  exact (hn M a ha ha1).trans (by simpa only [Real.rpow_one] using hLoss)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
