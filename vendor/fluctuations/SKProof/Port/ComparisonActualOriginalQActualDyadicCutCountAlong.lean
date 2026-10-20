module

public import ComparisonSignedCavityActualDyadicCutCountAlong
public import SKProof.Port.ComparisonActualOriginalQRetainedGammaPhysicalSources

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology BigOperators
set_option maxHeartbeats 10000000

namespace ActualThetaZeroOverlapMinimum

theorem eventually_actual_dyadic_cut_depth_log_bound_original_q
    {m delta cl cu Az C0 Ct D Bclock Cx : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,Cx*M.xs ≤ a → a ≤ 1 →
        (nativeDyadicCutDepth a:ℝ) ≤ (2+3/Real.log 2)*Real.log M.data.N := by
  have Hlower:=eventually_actual_minimum_scale_polynomial_lower_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=Cx) (q:=-(3:ℝ)) (r:=-(2:ℝ)) hCx (by norm_num))
  have HN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hlog:=(Real.tendsto_log_atTop.comp HN).eventually_ge_atTop 1
  filter_upwards [Hlower,Hcoef,Hlog] with n hnLower hnCoef hnLog
  intro M a ha ha1
  have ha0 : 0 < a:=(mul_pos hCx M.hxs).trans_le ha
  have Hpoly : M.data.N^(-(3:ℝ)) ≤ a:=by
    apply (show M.data.N^(-(3:ℝ)) ≤ Cx*M.data.N^(-(2:ℝ)) by
      simpa only [ActualHighWallData.N,one_mul] using hnCoef).trans
    exact (mul_le_mul_of_nonneg_left (hnLower M) hCx.le).trans ha
  exact nativeDyadicCutDepth_le_log_of_polynomial_lower ha0 ha1 M.data.hN hnLog Hpoly

theorem eventually_actual_dyadic_cut_depth_power_bound_original_q
    {m delta cl cu Az C0 Ct D Bclock Cx eps : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx) (heps : 0 < eps) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,Cx*M.xs ≤ a → a ≤ 1 → (nativeDyadicCutDepth a:ℝ) ≤ M.data.N^eps := by
  have Hlog:=eventually_actual_dyadic_cut_depth_log_bound_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hCx
  have HN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hloss:=HN.eventually (comparison_log_loss_eventually
    (C:=2+3/Real.log 2) (p:=1) (by have :=Real.log_pos (by norm_num : (1:ℝ) < 2);positivity) heps)
  filter_upwards [Hlog,Hloss] with n hn hLoss
  intro M a ha ha1
  exact (hn M a ha ha1).trans (by simpa only [ActualHighWallData.N,Real.rpow_one] using hLoss)

theorem eventually_actual_dyadic_cut_depth_log_bound_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Cx : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,Cx*M.xs ≤ a → a ≤ 1 →
        (nativeDyadicCutDepth a:ℝ) ≤ (2+3/Real.log 2)*Real.log M.data.N :=
  hdim.eventually (eventually_actual_dyadic_cut_depth_log_bound_original_q hm hC0 hCx)

theorem eventually_actual_dyadic_cut_depth_power_bound_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Cx eps : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx) (heps : 0 < eps)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,Cx*M.xs ≤ a → a ≤ 1 → (nativeDyadicCutDepth a:ℝ) ≤ M.data.N^eps :=
  hdim.eventually (eventually_actual_dyadic_cut_depth_power_bound_original_q hm hC0 hCx heps)

theorem eventually_actual_dyadic_cut_depth_saved_power_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Cx eps saving : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCx : 0 < Cx) (heps : 0 < eps)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀a : ℝ,Cx*M.xs ≤ a → a ≤ 1 →
        (nativeDyadicCutDepth a:ℝ)*M.data.N^(-saving) ≤ M.data.N^(-(saving-eps)) := by
  filter_upwards [eventually_actual_dyadic_cut_depth_power_bound_along_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 hCx heps dim hdim] with n hn
  intro M a ha ha1
  apply (mul_le_mul_of_nonneg_right (hn M a ha ha1) (Real.rpow_nonneg M.data.hN.le _)).trans_eq
  rw [←Real.rpow_add M.data.hN]
  congr 1
  ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
