module

public import ComparisonActualHighWallThetaZeroSweepBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ}

theorem eventually_theta_zero_sharp_wall_cost_of_original_density
    {m : ℝ} (hm : 0 < m) (hdelta : 0 < delta) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighWallData n delta,
      (n:ℝ)^(-(5:ℝ)/6+2*m) ≤ a.E →
      (∀lam∈Ioo ((n:ℝ)^(-10:ℝ)) (a.d^2),∀alpha : a.Profile,
        omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha=
        omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam →
        a.thetaZeroOriginalSweepDensity lam alpha ≤ (n:ℝ)^(10*delta)*a.E) →
      a.thetaZeroWallValue (a.d^2) (sq_pos_of_pos a.hd) le_rfl ≤
        realOrderedSKPathPressure n a.thetaZeroHighOnlyData.b
          a.thetaZeroHighOnlyData.h 0+(n:ℝ)^(20*delta)*a.E := by
  filter_upwards [eventually_actual_child_log_budget hm hdelta (by norm_num : (0:ℝ)<1),
    eventually_ge_atTop (1:ℕ)] with n hn hn1
  intro a hE hD
  have htau : 0 < (n:ℝ)^(-10:ℝ) := Real.rpow_pos_of_pos a.hN _
  have hN1 : (1:ℝ)≤(n:ℝ) := by exact_mod_cast hn1
  have htau1 : (n:ℝ)^(-10:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hd21 : a.d^2 ≤ 1 := by nlinarith only [a.hd,a.hd1]
  have Hbudget : a.thetaZeroSweepCost (a.d^2) ≤ (n:ℝ)^(20*delta)*a.E := by
    by_cases hsmall : a.d^2 ≤ (n:ℝ)^(-10:ℝ)
    · have hi := hn a.E ((n:ℝ)^(-10:ℝ))
        (by simpa only [one_pow,one_mul] using hE) le_rfl htau1
      rw [div_self htau.ne',Real.log_one,mul_zero,add_zero] at hi
      exact (a.theta_zero_sweep_cost_mem ⟨sq_nonneg a.d,le_rfl⟩).2.trans
        (hsmall.trans hi)
    · have hcut : (n:ℝ)^(-10:ℝ) ≤ a.d^2 := (lt_of_not_ge hsmall).le
      exact (a.theta_zero_sweep_cost_le_of_original_density htau hcut hD).trans
        (hn a.E (a.d^2) (by simpa only [one_pow,one_mul] using hE) hcut hd21)
  rw [a.theta_zero_wall_value_eq_bare_pressure_add_cost (a.d^2)
    (sq_pos_of_pos a.hd) le_rfl]
  exact add_le_add_right Hbudget _

theorem eventually_theta_zero_sharp_original_wall_of_original_density
    {m : ℝ} (hm : 0 < m) (hdelta : 0 < delta) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighWallData n delta,
      (n:ℝ)^(-(5:ℝ)/6+2*m) ≤ a.E →
      (∀lam∈Ioo ((n:ℝ)^(-10:ℝ)) (a.d^2),∀alpha : a.Profile,
        omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha=
        omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam →
        a.thetaZeroOriginalSweepDensity lam alpha ≤ (n:ℝ)^(10*delta)*a.E) →
      wallMinimumValue a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
        a.g a.hg.continuous a.T a.epsilon a.tau a.d n 0 0 ≤
        realOrderedSKPathPressure n a.thetaZeroHighOnlyData.b
          a.thetaZeroHighOnlyData.h 0+(n:ℝ)^(20*delta)*a.E := by
  filter_upwards [eventually_theta_zero_sharp_wall_cost_of_original_density
    (delta:=delta) hm hdelta] with n hn
  intro a hE hD
  rw [←a.theta_zero_full_value_eq_original_wall]
  exact hn a hE hD

theorem eventually_theta_zero_sharp_failure_selects_original_density
    {m : ℝ} (hm : 0 < m) (hdelta : 0 < delta) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighWallData n delta,
      (n:ℝ)^(-(5:ℝ)/6+2*m) ≤ a.E →
      realOrderedSKPathPressure n a.thetaZeroHighOnlyData.b
        a.thetaZeroHighOnlyData.h 0+(n:ℝ)^(20*delta)*a.E <
          a.thetaZeroWallValue (a.d^2) (sq_pos_of_pos a.hd) le_rfl →
      ∃lam∈Ioo ((n:ℝ)^(-10:ℝ)) (a.d^2),∃alpha : a.Profile,
        omittedComparisonSweepObjective a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam alpha=
        omittedComparisonSweepMinimum a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc
          a.hm a.hM n a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.d lam ∧
        (n:ℝ)^(10*delta)*a.E < a.thetaZeroOriginalSweepDensity lam alpha := by
  filter_upwards [eventually_theta_zero_sharp_wall_cost_of_original_density
    (delta:=delta) hm hdelta] with n hn
  intro a hE hfail
  by_contra hno
  push Not at hno
  exact not_lt_of_ge (hn a hE hno) hfail

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
