module

public import ComparisonActualHighWallThetaZeroHighOnlySourceClocks
public import ComparisonActualHighWallThetaZeroChildClockNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem changed_field_le_selected_strength
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.changedField u≤M.lam := by
  by_cases hs : u<M.data.s
  · have H : M.changedField u=0 := by
      change (0:ℝ)+omittedStrengthCoefficient M.data.d M.data.s
        (M.data.wallRadius M.alpha) M.lam u*M.data.wallRadius M.alpha u=0
      simp [omittedStrengthCoefficient,not_le.mpr hs]
    rw [H]
    exact M.hlam.le
  · have hr := M.data.wallRadius_bounds M.alpha u
    have hg := laplaceComparisonStrength_le M.data.d M.hlam.le
      (M.data.wallRadius M.alpha u)
    have hgp := (laplaceComparisonStrength_pos M.data.d M.hlam
      (M.data.wallRadius M.alpha u)).le
    have H := mul_le_mul_of_nonneg_left hr.2 hgp
    change (0:ℝ)+omittedStrengthCoefficient M.data.d M.data.s
      (M.data.wallRadius M.alpha) M.lam u*M.data.wallRadius M.alpha u≤M.lam
    simp only [omittedStrengthCoefficient,ite_eq_left (le_of_not_gt hs),zero_add]
    linarith only [H,hg]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
