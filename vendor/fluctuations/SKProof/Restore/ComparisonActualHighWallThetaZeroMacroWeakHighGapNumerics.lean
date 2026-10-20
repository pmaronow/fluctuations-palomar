module

public import SKProof.Restore.ComparisonActualHighWallThetaZeroMacroscopicHighOnlyExclusion
public import ComparisonActualHighWallThetaZeroMacroscopicEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem theta_zero_high_only_gap_of_reserve {c0:ℝ} (_hc0:0<c0)
    (hreserve:M.lam+(c0*M.xs)^2≤M.data.epsilon):
    ∀u∈Ico (0:ℝ) M.data.s,
      M.changedBare u+(c0*M.xs)^2≤M.changedBare M.data.s:=by
  intro u hu
  have Hlo:=M.data.theta_zero_changed_low_matrix M.lam M.hlam M.hld M.alpha hu.2
  have Hhi:=M.data.theta_zero_changed_high_matrix M.lam M.hlam M.hld M.alpha
    (le_refl M.data.s)
  change M.changedBare u=M.data.T-M.data.epsilon at Hlo
  change M.data.T-M.lam≤M.changedBare M.data.s at Hhi
  rw [Hlo]
  linarith only [Hhi,hreserve]

end ActualThetaZeroOverlapMinimum

theorem eventually_theta_zero_high_only_gap_of_weak_bounded_test
    {m delta cl cu Az C0 Ct D Bclock T c0:ℝ} {N:ℕ→ℕ}
    (hc0:0<c0) (hc0T:c0^2<T/4)
    (M:(j:ℕ)→ActualThetaZeroOverlapMinimum (N j+1) m delta cl cu Az C0 Ct D Bclock)
    (hxs:∀j,(M j).xs≤1)
    (hweak:Tendsto (fun j=>laplaceComparisonStrength (M j).data.d (M j).lam (M j).xs/(M j).xs^2)
      atTop (𝓝 0))
    (heps:∀ᶠj in atTop,T/4≤(M j).data.epsilon):
    ∀ᶠj in atTop,∀u∈Ico (0:ℝ) (M j).data.s,
      (M j).changedBare u+(c0*(M j).xs)^2≤(M j).changedBare (M j).data.s:=by
  have hlam:=actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    (Eventually.of_forall fun j=>⟨(M j).data.hd,(M j).hlam.le,(M j).hxs,hxs j,(M j).hld⟩) hweak
  have Hsmall:=hlam.eventually (gt_mem_nhds (sub_pos.mpr hc0T))
  filter_upwards [Hsmall,heps] with j hsmall hepsj
  have H0:0≤c0*(M j).xs:=mul_nonneg hc0.le (M j).hxs.le
  have Hx:c0*(M j).xs≤c0:=by simpa using mul_le_mul_of_nonneg_left (hxs j) hc0.le
  have Hsq:=pow_le_pow_left₀ H0 Hx 2
  have Hreserve:(M j).lam+(c0*(M j).xs)^2≤(M j).data.epsilon:=by
    linarith only [hsmall,hepsj,Hsq]
  exact (M j).theta_zero_high_only_gap_of_reserve hc0 Hreserve

end OAI.SKFluctuations.LaplaceWindowFormalization
