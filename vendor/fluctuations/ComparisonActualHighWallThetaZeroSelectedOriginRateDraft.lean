module

public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonActualHighWallThetaZeroSmallMassScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false

namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_rmin_over_selected_test_tendsto_zero_along_draft
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n => (Q n).data.rmin / (Q n).xs) atTop (𝓝 0) := by
  have Hpow : Tendsto (fun n => ((dim n+1:ℕ):ℝ)^(-(3*m)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show 0 < 3*m by positivity)).comp
      (tendsto_natCast_atTop_atTop.comp
        ((tendsto_add_atTop_nat 1).comp hdim))
  have Hlim := Hpow.const_mul (C0^3)
  simp only [mul_zero] at Hlim
  apply squeeze_zero (fun n => div_nonneg (Q n).data.hrbounds.1.le
    (Q n).hxs.le) _ Hlim
  intro n
  have H := (div_le_div_of_nonneg_right (Q n).radius_le_smallMass
    (Q n).hxs.le).trans ((Q n).small_mass_ratio hC0)
  simpa only [ActualHighWallData.N, neg_mul] using H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
