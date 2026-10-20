module

public import ComparisonNativeActualBadScaleMinimum
public import ComparisonNativeActualShellSharpChild

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
namespace NativeOverlapMinimum

theorem eventually_exists_actual_selected_bad_shell_child_from_target
    {margin delta cl cu Az C0 Ct D c0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcl1 : cl ≤ 1) (hcu1 : 1 ≤ cu)
    (hAz : 2 ≤ Az) (hCt : 1 ≤ Ct) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*margin-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D T)
        (x : ℝ) (hx : 0 < x),
      c0*x ≤ 1 → c0*x ≤ D →
      comparisonConditionalScale M.context.N delta M.context.E M.lam ≤ x →
      laplaceComparisonStrength M.context.d M.lam x ≤ x^2 →
      M.lam+(c0*x)^2 ≤ M.b 0 →
      ∀(ts : List ComparisonHistoryTerm) (epsilon shell : ℝ),
      (∀u,M.b u=historyMatrixClock T epsilon shell ts u) →
      (∀u,M.h u=historyFieldClock ts u) →
      (∀t∈ts,0 ≤ t.lam) → 0 ≤ epsilon →
      let child:=M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
      let bc:=fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
      let hc:=fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
      M.context.N^(20*delta)*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x <
        variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
          (n+1) bc hc child.d ((c0*x)^2) →
      ∃lam∈Ioo (child.N^(-10:ℝ)) ((c0*x)^2),∃alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) bc hc child.d lam alpha=
          variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
            (n+1) bc hc child.d lam ∧
        ∃Q : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D T,
          Q.context=child.toOverlapContext ∧ Q.lam=lam ∧ HEq Q.alpha alpha ∧
          Q.b=bc ∧ Q.h=hc ∧ Q.R=child.R alpha ∧
          Q.context.d=c0*x ∧
          Q.context.E=actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x ∧
          M.context.N^(delta/4)*M.context.E ≤ Q.context.E ∧
          Q.xs∈Icc (comparisonConditionalScale child.N delta child.E lam) 1 ∧
          Q.z=min (2*Q.xs) 1 ∧
          (Q.alpha.val.val Q.xs < cl*Q.xs ∨ cu*Q.xs < Q.alpha.val.val Q.xs) ∧
          (∀u,Q.b u=historyMatrixClock T epsilon shell (M.toHistoryTerm::ts) u) ∧
          (∀u,Q.h u=historyFieldClock (M.toHistoryTerm::ts) u) ∧
          (∀t∈M.toHistoryTerm::ts,0 ≤ t.lam) := by
  have hcu : 0 < cu:=zero_lt_one.trans_le hcu1
  have hclcu : cl ≤ cu:=hcl1.trans hcu1
  have hgamma : 0 < 1/C0:=one_div_pos.mpr hC0
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [eventually_actual_shell_child_failure_from_target (Bclock:=T) (T:=T)
    hm hdelta hroom hcl hcu hclcu hC0 hc0 hmargin,
    hs.eventually (eventually_actual_child_parameters_from_target hm hdelta hgamma hc0 hmargin)]
    with n hnFailure hnParams
  intro M x hx hchild1 hchildD htarget hweak hmatrix ts epsilon shell hbHist hhHist hlamHist hepsilon
  dsimp only
  intro hfail
  let child:=M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
  let bc:=fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
  let hc:=fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
  obtain ⟨lam,hlam,alpha,hattained,hbad⟩:=hnFailure M x hx hchild1 htarget hweak hmatrix
    ts epsilon shell hbHist hhHist hlamHist hepsilon hfail
  have hlo : (1/C0)*M.context.N^(-(2:ℝ)/3+margin)*M.context.d ≤ M.context.E:=by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.context.E ≤ M.context.d^2/Real.sqrt (n+1:ℕ):=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hp:=hnParams M.context.d M.lam M.context.E x M.context.hd M.hlam M.hld M.context.hE hx
    hlo hup htarget hweak
  have hchildLower : child.N^(-(2:ℝ)/3+margin)*child.d ≤ C0*child.E:=by
    have H:=mul_le_mul_of_nonneg_left hp.1 hC0.le
    change ((n+1:ℕ):ℝ)^(-(2:ℝ)/3+margin)*actualChildRadius c0 x ≤
      C0*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul] using H
  have hchildUpper : Real.sqrt child.N*child.E ≤ child.d^2:=by
    have H:=(le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mp hp.2.1
    change Real.sqrt M.context.N*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x ≤
      (actualChildRadius c0 x)^2
    simpa only [mul_comm] using H
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hroomChild : (c0*x)^2 ≤ bc 0:=by
    have H:=laplaceComparisonStrength_le M.context.d M.hlam.le (M.R 0)
    dsimp only [bc]
    linarith
  have hbChild : ∀u,bc u=historyMatrixClock T epsilon shell (M.toHistoryTerm::ts) u:=by
    intro u
    exact (M.inherited_shell_history_child_endpoint ts T epsilon shell hbHist hhHist u).1
  have hhChild : ∀u,hc u=historyFieldClock (M.toHistoryTerm::ts) u:=by
    intro u
    exact (M.inherited_shell_history_child_endpoint ts T epsilon shell hbHist hhHist u).2
  have hlamChild : ∀t∈M.toHistoryTerm::ts,0 ≤ t.lam:=by
    intro t ht
    rcases List.mem_cons.mp ht with ht|ht
    · subst t
      exact M.hlam.le
    · exact hlamHist t ht
  have htotal : ∀u∈Icc (0:ℝ) 1,hc u+bc u ≤ T:=by
    intro u _
    rw [hbChild,hhChild]
    change historyFieldAddition (M.toHistoryTerm::ts) u+
      (initialShellMatrixClock T epsilon shell u-historyMatrixReduction (M.toHistoryTerm::ts) u) ≤ T
    have hbase : initialShellMatrixClock T epsilon shell u ≤ T:=by
      unfold initialShellMatrixClock
      split_ifs <;> linarith
    linarith [actual_history_field_le_reduction (M.toHistoryTerm::ts) hlamChild u]
  have hlam0 : 0 < lam:=(Real.rpow_pos_of_pos child.hN _).trans hlam.1
  have hld : lam ≤ child.toOverlapContext.d^2:=hlam.2.le
  obtain ⟨Q,hcontext,hQlam,hAlpha,hbQ,hhQ,hRQ,hxs,hz,hbadQ⟩:=
    child.toOverlapContext.exists_selected_bad_scale_minimum_of_attained alpha bc hc
      hlam0 hld hdelta.le had.1 (hlam.2.le.trans hroomChild) had.2.1 had.2.2.2 hattained
      hchildD hchildUpper hchildLower htotal hAz hCt hcl1 hcu1 hbad
  refine ⟨lam,hlam,alpha,hattained,Q,hcontext,hQlam,hAlpha,hbQ,hhQ,hRQ,?_,?_,?_,hxs,hz,hbadQ,?_,?_,hlamChild⟩
  · rw [hcontext]
    rfl
  · rw [hcontext]
    rfl
  · rw [hcontext]
    exact hp.2.2.1
  · intro u
    rw [hbQ]
    exact hbChild u
  · intro u
    rw [hhQ]
    exact hhChild u

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
