module

public import ComparisonActualHighWallThetaZeroHighOnlyChildPullback
public import SKProof.Restore.ComparisonActualHighWallThetaZeroNativeChildCost
public import ComparisonActualHighOnlyRegularChildCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualThetaZeroOverlapMinimum

theorem eventually_theta_zero_high_only_child_cost_of_regular
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ hgap : ∀u∈Ico (0:ℝ) M.data.s,
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u+
            (c0*M.xs)^2 ≤
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b M.data.s-
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha M.data.s,
      c0*M.xs ≤ 1 → c0*M.xs ≤ D → M.data.s ≤ 1/4 →
      M.data.s ≤ comparisonLowerScale M.data.N
        (actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs) (c0*M.xs) →
      comparisonConditionalScale M.data.N delta M.data.E M.lam ≤ M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs ≤ M.xs^2 →
      (let child := M.highOnlyChildData hc0 hgap
       ∀lam ∈ Ioo (child.N^(-10:ℝ)) (child.d^2),∀alpha : child.Profile,
         child.objective lam alpha = child.minimum lam →
         ∀r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
           cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      M.highOnlyChildSweepCost hc0 hgap ≤ M.data.N^(20*delta)*
        actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs := by
  have hdim : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [ActualHighOnlyComparisonData.eventually_actual_high_only_regular_child_cost_of_regular
      (D:=D) (T:=Bclock) hm hdelta hroom hcl hcu hclcu hC0,
    hdim.eventually (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)] with n hnCost hnParams
  intro M hgap hchild1 hchildD hs4 hmass htarget hweak hregular
  let child := M.highOnlyChildData hc0 hgap
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
  have htotal : ∀u∈Icc (0:ℝ) 1,child.h u+child.b u ≤ Bclock :=
    M.changed_total_clock_le
  have hclock : ∀alpha : child.Profile,
      NativePullbackClockRegularity alpha.val.val child.b child.h 0 1 := by
    intro alpha
    exact M.changed_pullback_on_high_only_profile child alpha rfl
  change child.cost (child.d^2) ≤ child.N^(20*delta)*child.E
  exact hnCost child hchildD hchild1 hs4 hmass hchildUpper hchildLower
    htotal hclock hregular

theorem eventually_theta_zero_high_only_child_failure_selects_irregular
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ hgap : ∀u∈Ico (0:ℝ) M.data.s,
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u+
            (c0*M.xs)^2 ≤
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b M.data.s-
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha M.data.s,
      c0*M.xs ≤ 1 → c0*M.xs ≤ D → M.data.s ≤ 1/4 →
      M.data.s ≤ comparisonLowerScale M.data.N
        (actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs) (c0*M.xs) →
      comparisonConditionalScale M.data.N delta M.data.E M.lam ≤ M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs ≤ M.xs^2 →
      M.data.N^(20*delta)*actualChildErrorBudget (n+1) delta c0
        M.data.d M.lam M.xs < M.highOnlyChildSweepCost hc0 hgap →
      (let child := M.highOnlyChildData hc0 hgap
       ∃lam∈Ioo (child.N^(-10:ℝ)) (child.d^2),∃alpha : child.Profile,
         child.objective lam alpha = child.minimum lam ∧
         ∃r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
           alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) := by
  filter_upwards [eventually_theta_zero_high_only_child_cost_of_regular
      hm hdelta hroom hcl hcu hclcu hC0 hc0 hmargin] with n hn
  intro M hgap hchild1 hchildD hs4 hmass htarget hweak hfail
  dsimp only
  by_contra hno
  push Not at hno
  have hcost := hn M hgap hchild1 hchildD hs4 hmass htarget hweak (by
    exact hno)
  exact not_lt_of_ge hcost hfail

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
