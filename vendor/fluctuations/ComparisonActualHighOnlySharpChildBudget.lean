module

public import ComparisonActualHighOnlySweepBudget
public import ComparisonNativeActualChildBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighOnlyComparisonData
variable {m delta gamma : ℝ}

theorem eventually_cost_le_of_original_density
    (hm : 0 < m) (hdelta : 0 < delta) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ActualHighOnlyComparisonData n delta,
      a.d ≤ 1 →
      gamma * (n : ℝ)^(-(2 : ℝ)/3+m) * a.d ≤ a.E →
      a.E ≤ a.d^2 / Real.sqrt (n : ℝ) →
      (∀ lam ∈ Ioo ((n : ℝ)^(-10 : ℝ)) (a.d^2), ∀ alpha : a.Profile,
        a.objective lam alpha = a.minimum lam →
        a.originalSweepDensity lam alpha ≤ (n : ℝ)^(10*delta)*a.E) →
      a.cost (a.d^2) ≤ (n : ℝ)^(20*delta)*a.E := by
  filter_upwards [eventually_actual_child_log_budget hm hdelta hgamma] with n hn
  intro a hd1 hlo hup hD
  have hE := (comparison_parent_scale_lower_bounds a.hN hgamma a.hd hlo hup).2.1
  have htau : 0 < (n : ℝ)^(-10 : ℝ) := Real.rpow_pos_of_pos a.hN _
  have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast a.hn
  have htau1 : (n : ℝ)^(-10 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hd21 : a.d^2 ≤ 1 := by nlinarith only [a.hd,hd1]
  by_cases hsmall : a.d^2 ≤ (n : ℝ)^(-10 : ℝ)
  · have hi := hn a.E ((n : ℝ)^(-10 : ℝ)) hE le_rfl htau1
    rw [div_self htau.ne',Real.log_one,mul_zero,add_zero] at hi
    exact (a.cost_mem ⟨(sq_nonneg a.d),le_rfl⟩).2.trans (hsmall.trans hi)
  · have hcut : (n : ℝ)^(-10 : ℝ) ≤ a.d^2 := (lt_of_not_ge hsmall).le
    exact (a.cost_le_of_original_density htau hcut hD).trans
      (hn a.E (a.d^2) hE hcut hd21)

theorem eventually_failure_selects_original_density
    (hm : 0 < m) (hdelta : 0 < delta) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ActualHighOnlyComparisonData n delta,
      a.d ≤ 1 →
      gamma * (n : ℝ)^(-(2 : ℝ)/3+m) * a.d ≤ a.E →
      a.E ≤ a.d^2 / Real.sqrt (n : ℝ) →
      (n : ℝ)^(20*delta)*a.E < a.cost (a.d^2) →
      ∃ lam ∈ Ioo ((n : ℝ)^(-10 : ℝ)) (a.d^2), ∃ alpha : a.Profile,
        a.objective lam alpha = a.minimum lam ∧
        (n : ℝ)^(10*delta)*a.E < a.originalSweepDensity lam alpha := by
  filter_upwards [eventually_cost_le_of_original_density hm hdelta hgamma] with n hn
  intro a hd1 hlo hup hfail
  by_contra hno
  push Not at hno
  exact not_lt_of_ge (hn a hd1 hlo hup hno) hfail

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
