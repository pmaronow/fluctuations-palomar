module

public import SKProof.Restore.ComparisonActualHighWallThetaZeroHighOnlyChildCost
public import ComparisonActualHighOnlySelectedBadScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum

set_option maxHeartbeats 18000000 in
theorem eventually_exists_selected_bad_high_only_child_original_q
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ hgap : ∀u∈Ico (0:ℝ) M.data.s,
        M.changedBare u + (c0*M.xs)^2 ≤ M.changedBare M.data.s,
      c0*M.xs ≤ 1 → c0*M.xs ≤ D → M.data.s ≤ 1/4 →
      M.data.s ≤ comparisonLowerScale M.data.N
        (actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs) (c0*M.xs) →
      comparisonConditionalScale M.data.N delta M.data.E M.lam ≤ M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs ≤ M.xs^2 →
      M.data.N^(20*delta)*actualChildErrorBudget (n+1) delta c0
        M.data.d M.lam M.xs < M.highOnlyChildSweepCost hc0 hgap →
      ∃Q : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*M.xs ∧
        Q.context.E=actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs ∧
        M.data.N^(delta/4)*M.data.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N delta Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs<cl*Q.xs ∨ cu*Q.xs<Q.alpha.val.val Q.xs) ∧
        Q.data.s=M.data.s ∧ Q.b=M.changedBare ∧ Q.h=M.changedField := by
  have hdim : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [eventually_theta_zero_high_only_child_failure_selects_irregular
      hm hdelta hroom hcl hcu hclcu hC0 hc0 hmargin,
    hdim.eventually (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)] with n hnFailure hnParams
  intro M hgap hchild1 hchildD0 hs4 hmass htarget hweak hfail
  let child := M.highOnlyChildData hc0 hgap
  obtain ⟨lam,hlam,alpha,hattained,hbad⟩ :=
    hnFailure M hgap hchild1 hchildD0 hs4 hmass htarget hweak hfail
  have hlo : (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d ≤ M.data.E := by
    calc
      (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d =
          (M.data.N^(-(2:ℝ)/3+m)*M.data.d)/C0 := by ring
      _ ≤ M.data.E := (div_le_iff₀ hC0).mpr
        (by simpa only [mul_comm] using M.hlower)
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
  have hchildD : child.d ≤ D := by
    change c0*M.xs ≤ D
    exact hchildD0
  have hcl1 : cl ≤ 1 := by
    simpa only [M.alpha.property.2.1,mul_one] using
      (M.regular 1 ⟨M.hz.2,le_rfl⟩).1
  have hcu1 : 1 ≤ cu := by
    simpa only [M.alpha.property.2.1,mul_one] using
      (M.regular 1 ⟨M.hz.2,le_rfl⟩).2
  have htotal : ∀u∈Icc (0:ℝ) 1,child.h u+child.b u≤Bclock :=
    M.changed_total_clock_le
  have hlam0 : 0<lam := (Real.rpow_pos_of_pos child.hN _).trans hlam.1
  obtain ⟨_,_,hminimum⟩ := child.exists_minimum ⟨hlam0.le,hlam.2.le⟩
  let optimizer : ActualHighOnlyComparisonMinimum child lam := {
    alpha := alpha
    attained := hattained
    minimum := by
      intro beta
      calc
        child.objective lam alpha = child.minimum lam := hattained
        _ ≤ child.objective lam beta := hminimum beta
  }
  obtain ⟨Q,hcontext,hQlam,_hAlpha,hxs,_hz,hbadQ⟩ :=
    child.exists_selected_bad_scale_minimum_of_attained optimizer
      hlam0 hlam.2.le hdelta.le hchildD hchildUpper hchildLower
      htotal hAz hCt hcl1 hcu1 hbad
  refine ⟨Q,?_,?_,?_,?_,hbadQ,?_,?_,?_⟩
  · change Q.data.d=c0*M.xs
    rw [hcontext]
    rfl
  · change Q.data.E=actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs
    rw [hcontext]
    rfl
  · change M.data.N^(delta/4)*M.data.E≤Q.data.E
    rw [hcontext]
    exact hp.2.2.1
  · change Q.xs∈Icc (comparisonConditionalScale Q.data.N delta Q.data.E Q.lam) 1
    rw [hcontext,hQlam]
    exact hxs
  · rw [hcontext]
    rfl
  · change Q.data.b=M.changedBare
    rw [hcontext]
    rfl
  · change Q.data.h=M.changedField
    rw [hcontext]
    rfl

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
