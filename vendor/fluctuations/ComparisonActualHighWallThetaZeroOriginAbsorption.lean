module

public import ComparisonActualHighWallThetaZeroOriginPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem eventually_initial_origin_squared_price
    (hm:0 < m) (hdelta:0 < delta) (hC0:0 < C0):
    ∀ᶠn:ℕ in atTop,
      ∀Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      Q.data.s≤Q.data.d→
      Q.lam*Q.data.rmin^2*Q.data.s≤Q.data.N^delta*Q.data.E := by
  have HP0:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=1)
      (q:=-3*m) (r:=delta) (by norm_num) (by linarith))
  have HP:∀ᶠn:ℕ in atTop,C0^3*((n+1:ℕ):ℝ)^(-3*m)≤((n+1:ℕ):ℝ)^delta:=by
    simpa only [one_mul] using HP0
  filter_upwards [HP] with n hn
  intro Q hsd
  have H:=Q.initial_origin_squared_price hC0 hsd
  exact H.trans (mul_le_mul_of_nonneg_right hn Q.data.hE.le)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
