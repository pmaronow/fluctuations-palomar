module

public import ComparisonActualHighWallNativeChildPullback
public import ComparisonActualHighWallMacroscopicAllMassChildFactory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem eventually_all_mass_child_cost_of_regular
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      c0*M.xs ≤ 1 →
      comparisonConditionalScale M.data.N delta M.data.E (M.data.d^2) ≤ M.xs →
      M.data.g M.xs ≤ M.xs^2 → (c0*M.xs)^2 ≤ M.data.b M.alpha 0 →
      let child := M.macroChildNumerics hc0
      (∀ lam ∈ Ioo (child.N^(-10 : ℝ)) ((c0*M.xs)^2),∀ alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) (M.data.b M.alpha) (M.data.h M.alpha) child.d lam alpha =
        variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
          (n+1) (M.data.b M.alpha) (M.data.h M.alpha) child.d lam →
        ∀ r ∈ Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      M.macroAllMassChildSweepCost hc0 ≤ M.data.N^(20*delta)*
        actualChildErrorBudget (n+1) delta c0 M.data.d (M.data.d^2) M.xs := by
  have hs : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [eventually_actual_regular_child_cost_of_regular (T := Bclock)
      hm hdelta hroom hcl hcu hclcu hC0,
    hs.eventually (eventually_actual_child_parameters_from_target
      hm hdelta (one_div_pos.mpr hC0) hc0 hmargin)] with n hnCost hnParams
  intro M hchild1 htarget hweak hmatrix
  dsimp only
  intro hregular
  let child := M.macroChildNumerics hc0
  have hlo : (1/C0)*M.data.N^(-(2 : ℝ)/3+m)*M.data.d ≤ M.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.data.E ≤ M.data.d^2/Real.sqrt ((n+1 : ℕ) : ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hp := hnParams M.data.d (M.data.d^2) M.data.E M.xs M.data.hd
    (sq_pos_of_pos M.data.hd) le_rfl M.data.hE M.hxs hlo hup htarget hweak
  have hchildLower : child.N^(-(2 : ℝ)/3+m)*child.d ≤ C0*child.E := by
    have H := mul_le_mul_of_nonneg_left hp.1 hC0.le
    change ((n+1 : ℕ) : ℝ)^(-(2 : ℝ)/3+m)*actualChildRadius c0 M.xs ≤
      C0*actualChildErrorBudget (n+1) delta c0 M.data.d (M.data.d^2) M.xs
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul] using H
  have hchildUpper : Real.sqrt child.N*child.E ≤ child.d^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mp hp.2.1
    change Real.sqrt M.data.N*actualChildErrorBudget (n+1) delta c0 M.data.d (M.data.d^2) M.xs ≤
      (actualChildRadius c0 M.xs)^2
    simpa only [mul_comm] using H
  have HC := M.data.admissible M.alpha
  have Htotal : ∀ u ∈ Icc (0 : ℝ) 1,M.data.h M.alpha u+M.data.b M.alpha u ≤ Bclock := by
    intro u hu
    rw [←(M.data.clock_coe M.alpha hu).1,←(M.data.clock_coe M.alpha hu).2]
    exact (M.data.total_clock_le M.alpha u hu).trans M.hT
  exact hnCost child (M.data.b M.alpha) (M.data.h M.alpha) ((c0*M.xs)^2)
    (sq_pos_of_pos (mul_pos hc0 M.hxs)) le_rfl hchild1 hmatrix HC.1 HC.2.1 HC.2.2.2
    hchildUpper hchildLower (M.data.changed_pullback_on_native_child_profile M.alpha child)
    Htotal hregular

theorem eventually_all_mass_child_failure_selects_irregular
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      c0*M.xs ≤ 1 →
      comparisonConditionalScale M.data.N delta M.data.E (M.data.d^2) ≤ M.xs →
      M.data.g M.xs ≤ M.xs^2 → (c0*M.xs)^2 ≤ M.data.b M.alpha 0 →
      M.data.N^(20*delta)*actualChildErrorBudget (n+1) delta c0 M.data.d (M.data.d^2) M.xs <
        M.macroAllMassChildSweepCost hc0 →
      let child := M.macroChildNumerics hc0
      ∃ lam ∈ Ioo (child.N^(-10 : ℝ)) ((c0*M.xs)^2),∃ alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) (M.data.b M.alpha) (M.data.h M.alpha) child.d lam alpha =
        variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
          (n+1) (M.data.b M.alpha) (M.data.h M.alpha) child.d lam ∧
        ∃ r ∈ Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r := by
  filter_upwards [eventually_all_mass_child_cost_of_regular hm hdelta hroom hcl hcu hclcu hC0 hc0 hmargin]
    with n hn
  intro M hchild1 htarget hweak hmatrix hfail
  dsimp only
  by_contra hno
  push Not at hno
  exact not_lt_of_ge (hn M hchild1 htarget hweak hmatrix (by
    intro lam hlam alpha hattained r hr
    exact hno lam hlam alpha hattained r hr)) hfail

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
