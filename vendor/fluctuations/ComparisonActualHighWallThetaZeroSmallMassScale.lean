module

public import ComparisonActualHighWallThetaZeroSelectedScale
public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem small_mass_ratio
    (Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0:0 < C0) :
    comparisonSmallMass Q.data.N Q.data.E/Q.xs≤
      C0^3*Q.data.N^(-3*m) := by
  have hupper:Q.data.E≤Q.data.d^2/Real.sqrt Q.data.N:=
    (le_div_iff₀ (Real.sqrt_pos.mpr Q.data.hN)).mpr
      (by simpa only [mul_comm] using Q.hupper)
  have hlower:(1/C0)*Q.data.N^(-(2:ℝ)/3+m)*Q.data.d≤Q.data.E:=by
    have H:(Q.data.N^(-(2:ℝ)/3+m)*Q.data.d)/C0≤Q.data.E:=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using Q.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have H:=comparison_radius_small_mass_ratio Q.data.hN
    (one_div_pos.mpr hC0) Q.data.hd hlower hupper Q.hscale
  simpa only [one_div_div,one_pow,div_pow,div_one,ActualHighWallData.N] using H

theorem eventually_small_mass_le_xs
    (hm:0 < m) (hC0:0 < C0) :
    ∀ᶠn:ℕ in atTop,
      ∀Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        comparisonSmallMass Q.data.N Q.data.E≤Q.xs := by
  have hs:Tendsto (fun n:ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  have hUn:=hs.eventually (eventually_coefficient_rpow_le
    (c:=C0^3) (d:=1) (q:=-3*m) (r:=0)
    (by norm_num) (by linarith))
  filter_upwards [hUn] with n hn
  intro Q
  have Hratio:=Q.small_mass_ratio hC0
  simp only [Real.rpow_zero,one_mul] at hn
  have Hbound:C0^3*Q.data.N^(-3*m)≤1:=by
    simpa only [ActualHighWallData.N] using hn
  exact (div_le_one Q.hxs).mp (Hratio.trans Hbound)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
