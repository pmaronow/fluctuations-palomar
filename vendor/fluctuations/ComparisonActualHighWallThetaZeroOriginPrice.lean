module

public import ComparisonActualHighWallThetaZeroBarePullback
public import ComparisonNativeStarCapSaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem initial_origin_squared_price (hC0:0<C0) (hsd:Q.data.s≤Q.data.d):
    Q.lam*Q.data.rmin^2*Q.data.s ≤
      C0^3*Q.data.N^(-3*m)*Q.data.E := by
  let a:=Q.data
  let U:=comparisonSmallMass a.N a.E
  let gamma:=1/C0
  have hgamma:0<gamma:=one_div_pos.mpr hC0
  have hlo:gamma*a.N^(-(2:ℝ)/3+m)*a.d≤a.E:=by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using Q.hlower)
    simpa only [gamma,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hratio:=comparison_star_cubic_ratio a.hN hgamma a.hd a.hE hlo
  have Hratio':a.d^3/(a.N^2*a.E^3)≤C0^3*a.N^(-3*m):=by
    convert Hratio using 1
    dsimp only [gamma]
    field_simp
  have hU:0<U:=comparisonSmallMass_pos a.hN a.hE
  have hr:a.rmin≤U:=a.theta_zero_radius_le_smallMass
  have hsq:a.rmin^2≤U^2:=pow_le_pow_left₀ a.hrbounds.1.le hr 2
  have H0:Q.lam*a.rmin^2*a.s≤a.d^3*U^2:=by
    have H1:Q.lam*a.rmin^2*a.s≤a.d^2*U^2*a.d:=by
      gcongr
      · exact a.hs.1.le
      · exact Q.hld
    nlinarith only [H1]
  have HE:a.d^3*U^2=(a.d^3/(a.N^2*a.E^3))*a.E:=by
    dsimp only [U,comparisonSmallMass]
    field_simp
  rw [HE] at H0
  exact H0.trans (mul_le_mul_of_nonneg_right Hratio' a.hE.le)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
