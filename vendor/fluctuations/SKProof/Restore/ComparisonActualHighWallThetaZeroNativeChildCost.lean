module

public import ComparisonActualHighWallThetaZeroNativeChildPullback
public import ComparisonNativeActualRegularChildSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem changed_total_clock_le :
    let P := M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
    ∀u ∈ Icc (0:ℝ) 1,
      (P.h u+P.coefficient M.alpha u*P.R M.alpha u)+
        (P.b u-P.coefficient M.alpha u) ≤ Bclock := by
  dsimp only
  let P := M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  intro u hu
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
  rw [hh]
  linarith only [hb,hmult,M.hT]

end ActualThetaZeroOverlapMinimum

theorem eventually_theta_zero_all_mass_child_cost_of_regular
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      c0*M.xs ≤ 1 →
      comparisonConditionalScale M.data.N delta M.data.E M.lam ≤ M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs ≤ M.xs^2 →
      (c0*M.xs)^2 ≤
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b 0-
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha 0 →
      (let child := M.allMassChildNumerics hc0
       let P := M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
       ∀lam ∈ Ioo (child.N^(-10:ℝ)) ((c0*M.xs)^2),∀alpha : child.Profile,
         variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
           (n+1) (fun u=>P.b u-P.coefficient M.alpha u)
           (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) child.d lam alpha =
         variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
           (n+1) (fun u=>P.b u-P.coefficient M.alpha u)
           (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) child.d lam →
         ∀r ∈ Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
           cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      M.allMassChildSweepCost hc0 ≤ M.data.N^(20*delta)*
        actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs := by
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [eventually_actual_regular_child_cost_of_regular (T:=Bclock)
      hm hdelta hroom hcl hcu hclcu hC0,
    hs.eventually (eventually_actual_child_parameters_from_target
      hm hdelta (one_div_pos.mpr hC0) hc0 hmargin)] with n hnCost hnParams
  intro M hchild1 htarget hweak hmatrix
  dsimp only
  intro hregular
  let P := M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  let child := M.allMassChildNumerics hc0
  have hlo : (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d ≤ M.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.data.E ≤ M.data.d^2/Real.sqrt ((n+1:ℕ):ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr
      (by simpa only [mul_comm] using M.hupper)
  have hp := hnParams M.data.d M.lam M.data.E M.xs M.data.hd M.hlam M.hld
    M.data.hE M.hxs hlo hup htarget hweak
  have hchildLower : child.N^(-(2:ℝ)/3+m)*child.d ≤ C0*child.E := by
    have H := mul_le_mul_of_nonneg_left hp.1 hC0.le
    change ((n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*actualChildRadius c0 M.xs ≤
      C0*actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul] using H
  have hchildUpper : Real.sqrt child.N*child.E ≤ child.d^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mp hp.2.1
    change Real.sqrt M.data.N*actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs ≤
      (actualChildRadius c0 M.xs)^2
    simpa only [mul_comm] using H
  have had := P.clockAdmissible M.alpha
  exact hnCost child (fun u=>P.b u-P.coefficient M.alpha u)
    (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) ((c0*M.xs)^2)
    (sq_pos_of_pos (mul_pos hc0 M.hxs)) le_rfl hchild1 hmatrix
    had.1 had.2.1 (had.2.2.2 0 (by norm_num))
    hchildUpper hchildLower
    (fun beta=>M.changed_pullback_on_native_child_profile child beta)
    M.changed_total_clock_le hregular

theorem eventually_theta_zero_all_mass_child_failure_selects_irregular
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      c0*M.xs ≤ 1 →
      comparisonConditionalScale M.data.N delta M.data.E M.lam ≤ M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs ≤ M.xs^2 →
      (c0*M.xs)^2 ≤
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b 0-
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha 0 →
      M.data.N^(20*delta)*actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs <
        M.allMassChildSweepCost hc0 →
      (let child := M.allMassChildNumerics hc0
       let P := M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
       ∃lam ∈ Ioo (child.N^(-10:ℝ)) ((c0*M.xs)^2),∃alpha : child.Profile,
         variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
           (n+1) (fun u=>P.b u-P.coefficient M.alpha u)
           (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) child.d lam alpha =
         variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
           (n+1) (fun u=>P.b u-P.coefficient M.alpha u)
           (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u) child.d lam ∧
         ∃r ∈ Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
           alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) := by
  filter_upwards [eventually_theta_zero_all_mass_child_cost_of_regular
    hm hdelta hroom hcl hcu hclcu hC0 hc0 hmargin] with n hn
  intro M hchild1 htarget hweak hmatrix hfail
  dsimp only
  by_contra hno
  push Not at hno
  exact not_lt_of_ge (hn M hchild1 htarget hweak hmatrix (by
    exact hno)) hfail

end OAI.SKFluctuations.LaplaceWindowFormalization
