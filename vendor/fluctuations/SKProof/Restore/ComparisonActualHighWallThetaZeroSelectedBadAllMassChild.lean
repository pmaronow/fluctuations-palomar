module

public import SKProof.Restore.ComparisonActualHighWallThetaZeroNativeChildCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem eventually_exists_selected_bad_theta_zero_all_mass_child
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      c0*M.xs ≤ 1 → c0*M.xs ≤ D →
      comparisonConditionalScale M.data.N delta M.data.E M.lam ≤ M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs ≤ M.xs^2 → (c0*M.xs)^2 ≤ (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b 0-(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha 0 →
      M.data.N^(20*delta)*actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs <
        M.allMassChildSweepCost hc0 →
      ∃ Q : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.context.d = c0*M.xs ∧
        Q.context.E = actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs ∧
        M.data.N^(delta/4)*M.data.E ≤ Q.context.E ∧
        Q.xs ∈ Icc (comparisonConditionalScale Q.context.N delta Q.context.E Q.lam) 1 ∧
        Q.z = min (2*Q.xs) 1 ∧
        (Q.alpha.val.val Q.xs < cl*Q.xs ∨ cu*Q.xs < Q.alpha.val.val Q.xs) ∧
        Q.b = (fun u=>(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u) ∧ Q.h = (fun u=>(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).h u+(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u*(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).R M.alpha u) := by
  have hcu : 0 < cu := zero_lt_one.trans_le hcu1
  have hclcu : cl ≤ cu := hcl1.trans hcu1
  have hs : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [eventually_theta_zero_all_mass_child_failure_selects_irregular hm hdelta hroom hcl hcu hclcu hC0 hc0 hmargin,
    hs.eventually (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)] with n hnFailure hnParams
  intro M hchild1 hchildD htarget hweak hmatrix hfail
  let child := M.allMassChildNumerics hc0
  obtain ⟨lam,hlam,alpha,hattained,hbad⟩ := hnFailure M hchild1 htarget hweak hmatrix hfail
  have hlo : (1/C0)*M.data.N^(-(2 : ℝ)/3+m)*M.data.d ≤ M.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.data.E ≤ M.data.d^2/Real.sqrt ((n+1 : ℕ) : ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hp := hnParams M.data.d M.lam M.data.E M.xs M.data.hd
    M.hlam M.hld M.data.hE M.hxs hlo hup htarget hweak
  have hchildLower : child.N^(-(2 : ℝ)/3+m)*child.d ≤ C0*child.E := by
    have H := mul_le_mul_of_nonneg_left hp.1 hC0.le
    change ((n+1 : ℕ) : ℝ)^(-(2 : ℝ)/3+m)*actualChildRadius c0 M.xs ≤
      C0*actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul] using H
  have hchildUpper : Real.sqrt child.N*child.E ≤ child.d^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mp hp.2.1
    change Real.sqrt M.data.N*actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs ≤
      (actualChildRadius c0 M.xs)^2
    simpa only [mul_comm] using H
  have HC := (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).clockAdmissible M.alpha
  have Htotal := M.changed_total_clock_le
  have hcl1 : cl ≤ 1 := by
    simpa only [M.alpha.property.2.1,mul_one] using (M.regular 1 ⟨M.hz.2,le_rfl⟩).1
  have hcu1 : 1 ≤ cu := by
    simpa only [M.alpha.property.2.1,mul_one] using (M.regular 1 ⟨M.hz.2,le_rfl⟩).2
  have hlam0 : 0 < lam := (Real.rpow_pos_of_pos child.hN _).trans hlam.1
  obtain ⟨Q,hcontext,hQlam,hAlpha,hbQ,hhQ,hRQ,hxs,hz,hbadQ⟩ :=
    child.toOverlapContext.exists_selected_bad_scale_minimum_of_attained alpha
      (fun u=>(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u)
      (fun u=>(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).h u+(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u*(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).R M.alpha u)
      hlam0 hlam.2.le hdelta.le HC.1 (hlam.2.le.trans hmatrix) HC.2.1 (HC.2.2.2 0 ⟨le_rfl,zero_le_one⟩) hattained
      hchildD hchildUpper hchildLower Htotal hAz hCt hcl1 hcu1 hbad
  refine ⟨Q,?_,?_,?_,?_,hz,hbadQ,hbQ,hhQ⟩
  · rw [hcontext];rfl
  · rw [hcontext];rfl
  · rw [hcontext];exact hp.2.2.1
  · rw [hcontext,hQlam];exact hxs

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
