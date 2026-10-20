module

public import ComparisonActualHighWallThetaZeroHighOnlyChildPullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem changed_total_clock_le_temperature {u : ℝ} (_hu : u∈Icc (0:ℝ) 1) :
    M.changedField u+M.changedBare u ≤ M.data.T := by
  let P := M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  have hR : P.R M.alpha u ≤ 1 :=
    (omittedSweepQuantile_bounds M.data.hr ⟨M.data.hs.1.le,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha u).2
  have he : 0 ≤ P.coefficient M.alpha u := by
    change 0 ≤ omittedStrengthCoefficient M.data.d M.data.s
      (M.data.wallRadius M.alpha) M.lam u
    unfold omittedStrengthCoefficient
    split_ifs
    · exact (laplaceComparisonStrength_pos M.data.d M.hlam _).le
    · exact le_rfl
  have hb : P.b u ≤ M.data.T := by
    change wallBareMatrix M.data.T M.data.epsilon 0 M.data.s u ≤ M.data.T
    unfold wallBareMatrix
    split_ifs
    · have hε : 0 ≤ M.data.epsilon := M.data.hepsilon.1.le
      simp only [zero_mul,sub_zero]
      linarith only [hε]
    · exact le_rfl
  have hh : P.h u = 0 := rfl
  have hmult := mul_le_mul_of_nonneg_left hR he
  change (P.h u+P.coefficient M.alpha u*P.R M.alpha u)+
    (P.b u-P.coefficient M.alpha u) ≤ M.data.T
  rw [hh]
  linarith only [hb,hmult]

theorem changed_root_field_zero : M.changedField 0 = 0 := by
  change (0:ℝ)+omittedStrengthCoefficient M.data.d M.data.s
    (M.data.wallRadius M.alpha) M.lam 0*M.data.wallRadius M.alpha 0=0
  simp [omittedStrengthCoefficient,not_le.mpr M.data.hs.1]

theorem changed_field_le_strength {u : ℝ} (_hu : u∈Icc (0:ℝ) 1) :
    M.changedField u ≤ M.data.d^2 := by
  by_cases hs : u < M.data.s
  · have H : M.changedField u = 0 := by
      change (0:ℝ)+omittedStrengthCoefficient M.data.d M.data.s
        (M.data.wallRadius M.alpha) M.lam u*M.data.wallRadius M.alpha u=0
      simp [omittedStrengthCoefficient,not_le.mpr hs]
    rw [H]
    exact (sq_nonneg _)
  · have hr := M.data.wallRadius_bounds M.alpha u
    have hg := laplaceComparisonStrength_le M.data.d M.hlam.le
      (M.data.wallRadius M.alpha u)
    have hgp := (laplaceComparisonStrength_pos M.data.d M.hlam
      (M.data.wallRadius M.alpha u)).le
    have H := mul_le_mul_of_nonneg_left hr.2 hgp
    have H' : laplaceComparisonStrength M.data.d M.lam
        (M.data.wallRadius M.alpha u)*M.data.wallRadius M.alpha u ≤ M.data.d^2 := by
      nlinarith only [H,hg,M.hld]
    change (0:ℝ)+omittedStrengthCoefficient M.data.d M.data.s
      (M.data.wallRadius M.alpha) M.lam u*M.data.wallRadius M.alpha u ≤ M.data.d^2
    simp only [omittedStrengthCoefficient,ite_eq_left (le_of_not_gt hs),zero_add]
    exact H'

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
