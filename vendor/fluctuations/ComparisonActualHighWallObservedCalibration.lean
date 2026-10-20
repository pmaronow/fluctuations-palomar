module

public import ComparisonActualHighWallObservedInnovation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock v : ℝ}

theorem observed_fixed_calibration_scales
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hn : 2≤ n) (hm : 0≤ m) (hC0 : 0< C0) (hdv : M.data.d≤ v) (_hv1 : v≤1) :
    (n:ℝ)^(-(1:ℝ)/6+m)≤ (2*C0)*M.xs ∧
      (1/24)*M.data.d^3/Real.log (n:ℝ)≤ M.data.g v*v/(12*Real.log M.data.N) := by
  constructor
  · have HH:=observed_critical_power_succ (by omega : 1≤ n)
      (show -1≤-(1:ℝ)/6+m by linarith)
    have HC:=actual_high_wall_original_boundary_critical_radius hC0 M
    nlinarith only [HH,HC]
  · have hd:=M.data.hd
    have hv : 0< v:=hd.trans_le hdv
    have HD : M.data.d^3/v≤ M.data.d^2:=(div_le_iff₀ hv).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left hdv (sq_nonneg M.data.d)])
    have HG : M.data.d^3/v≤ M.data.g v:=
      (min_eq_right HD).symm.le.trans (laplaceComparisonStrength_lower hd (sq_pos_of_pos hd) hv)
    have Hstrength : M.data.d^3≤ M.data.g v*v:=(div_le_iff₀ hv).mp HG
    have hnR : (2:ℝ)≤ n:=by exact_mod_cast hn
    have hlog : 0< Real.log (n:ℝ):=Real.log_pos (by linarith)
    have hlogN : 0< Real.log M.data.N:=by apply Real.log_pos;change 1< ((n+1:ℕ):ℝ);exact_mod_cast (by omega : 1< n+1)
    have Hlog:=observed_log_succ_le_twice hn
    calc
      _=M.data.d^3/(24*Real.log (n:ℝ)):=by ring
      _≤ M.data.d^3/(12*Real.log M.data.N):=
        div_le_div_of_nonneg_left (pow_nonneg hd.le _) (by positivity) (by dsimp only [ActualHighWallData.N];linarith)
      _≤_:=div_le_div_of_nonneg_right Hstrength (by positivity)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
