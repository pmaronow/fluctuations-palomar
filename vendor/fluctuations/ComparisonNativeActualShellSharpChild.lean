module

public import ComparisonNativeActualShellChildClocks
public import ComparisonNativeActualShellChildBudget
public import ComparisonNativeActualMinimumChild
public import ComparisonNativeActualChildParameterGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 11000000
namespace NativeOverlapMinimum

theorem eventually_actual_shell_child_cost_from_target
    {margin delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*margin-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (x : ℝ) (hx : 0 < x),
      c0*x ≤ 1 → comparisonConditionalScale M.context.N delta M.context.E M.lam ≤ x →
      laplaceComparisonStrength M.context.d M.lam x ≤ x^2 →
      M.lam+(c0*x)^2 ≤ M.b 0 →
      ∀(ts : List ComparisonHistoryTerm) (epsilon shell : ℝ),
      (∀u,M.b u=historyMatrixClock T epsilon shell ts u) →
      (∀u,M.h u=historyFieldClock ts u) →
      (∀t∈ts,0 ≤ t.lam) → 0 ≤ epsilon →
      let child := M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
      let bc := fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
      let hc := fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
      (∀lam∈Ioo (child.N^(-10:ℝ)) ((c0*x)^2),∀alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) bc hc child.d lam alpha=
          variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
            (n+1) bc hc child.d lam →
        ∀r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
        (n+1) bc hc child.d ((c0*x)^2) ≤
          M.context.N^(20*delta)*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x := by
  have hgamma : 0 < 1/C0 := one_div_pos.mpr hC0
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  filter_upwards [eventually_actual_shell_history_child_cost_of_regular (T:=T) hm hdelta hroom hcl hcu hclcu hC0,
    hs.eventually (eventually_actual_child_parameters_from_target hm hdelta hgamma hc0 hmargin)]
    with n hncost hnparams
  intro M x hx hchild1 htarget hweak hmatrix ts epsilon shell hbHist hhHist hlamHist hepsilon
  dsimp only
  intro hregular
  let child := M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
  let bc := fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
  let hc := fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
  have hlo : (1/C0)*M.context.N^(-(2:ℝ)/3+margin)*M.context.d ≤ M.context.E := by
    have hh := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
  have hup : M.context.E ≤ M.context.d^2/Real.sqrt (n+1:ℕ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hp := hnparams M.context.d M.lam M.context.E x M.context.hd M.hlam M.hld M.context.hE hx
    hlo hup htarget hweak
  have hchildLower : child.N^(-(2:ℝ)/3+margin)*child.d ≤ C0*child.E := by
    have hh := mul_le_mul_of_nonneg_left hp.1 hC0.le
    change ((n+1:ℕ):ℝ)^(-(2:ℝ)/3+margin)*actualChildRadius c0 x ≤
      C0*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul] using hh
  have hchildUpper : Real.sqrt child.N*child.E ≤ child.d^2 := by
    have hh := (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mp hp.2.1
    change Real.sqrt M.context.N*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x ≤
      (actualChildRadius c0 x)^2
    simpa only [mul_comm] using hh
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hroom' : (c0*x)^2 ≤ bc 0 := by
    have he := laplaceComparisonStrength_le M.context.d M.hlam.le (M.R 0)
    dsimp [bc]
    linarith
  have hbChild : ∀u,bc u=historyMatrixClock T epsilon shell (M.toHistoryTerm::ts) u := by
    intro u
    exact (M.inherited_shell_history_child_endpoint ts T epsilon shell hbHist hhHist u).1
  have hhChild : ∀u,hc u=historyFieldClock (M.toHistoryTerm::ts) u := by
    intro u
    exact (M.inherited_shell_history_child_endpoint ts T epsilon shell hbHist hhHist u).2
  have hlamChild : ∀t∈M.toHistoryTerm::ts,0 ≤ t.lam := by
    intro t ht
    rcases List.mem_cons.mp ht with ht|ht
    · subst t
      exact M.hlam.le
    · exact hlamHist t ht
  exact hncost child bc hc ((c0*x)^2) (sq_pos_of_pos (mul_pos hc0 hx)) le_rfl hchild1 hroom'
    had.1 had.2.1 had.2.2.2 hchildUpper hchildLower
    (M.toHistoryTerm::ts) epsilon shell hbChild hhChild hlamChild hepsilon hregular

theorem eventually_actual_shell_child_failure_from_target
    {margin delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*margin-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (x : ℝ) (hx : 0 < x),
      c0*x ≤ 1 → comparisonConditionalScale M.context.N delta M.context.E M.lam ≤ x →
      laplaceComparisonStrength M.context.d M.lam x ≤ x^2 →
      M.lam+(c0*x)^2 ≤ M.b 0 →
      ∀(ts : List ComparisonHistoryTerm) (epsilon shell : ℝ),
      (∀u,M.b u=historyMatrixClock T epsilon shell ts u) →
      (∀u,M.h u=historyFieldClock ts u) →
      (∀t∈ts,0 ≤ t.lam) → 0 ≤ epsilon →
      let child := M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
      let bc := fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
      let hc := fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
      M.context.N^(20*delta)*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x <
        variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
          (n+1) bc hc child.d ((c0*x)^2) →
      ∃lam∈Ioo (child.N^(-10:ℝ)) ((c0*x)^2),∃alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) bc hc child.d lam alpha=
          variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
            (n+1) bc hc child.d lam ∧
        ∃r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r := by
  filter_upwards [eventually_actual_shell_child_cost_from_target (T:=T) hm hdelta hroom
    hcl hcu hclcu hC0 hc0 hmargin] with n hn
  intro M x hx hchild1 htarget hweak hmatrix ts epsilon shell hbHist hhHist hlamHist hepsilon
  dsimp only
  intro hfail
  by_contra hno
  push Not at hno
  have hcost:=hn M x hx hchild1 htarget hweak hmatrix ts epsilon shell
    hbHist hhHist hlamHist hepsilon (by
      intro lam hlam alpha hattained r hr
      exact hno lam hlam alpha hattained r hr)
  exact not_lt_of_ge hcost hfail

theorem eventually_exists_actual_shell_sharp_child
    {margin delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*margin-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (x : ℝ) (hx : 0 < x),
      c0*x ≤ 1 → comparisonConditionalScale M.context.N delta M.context.E M.lam ≤ x →
      laplaceComparisonStrength M.context.d M.lam x ≤ x^2 →
      M.lam+(c0*x)^2 ≤ M.b 0 →
      ∀(ts : List ComparisonHistoryTerm) (epsilon shell : ℝ),
      (∀u,M.b u=historyMatrixClock T epsilon shell ts u) →
      (∀u,M.h u=historyFieldClock ts u) →
      (∀t∈ts,0 ≤ t.lam) → 0 ≤ epsilon →
      let child := M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
      let bc := fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
      let hc := fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
      (∀lam∈Ioo (child.N^(-10:ℝ)) ((c0*x)^2),∀alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) bc hc child.d lam alpha=
          variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
            (n+1) bc hc child.d lam →
        ∀r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      ∃beta : child.Profile,∃a : NativeChildBarrierCall (n+1) delta,
        a.context=M.context.toChildBarrierParameters ∧ a.lam=M.lam ∧ HEq a.alpha M.alpha ∧
        a.R=M.R ∧ a.b=M.b ∧ a.h=M.h ∧ a.childRadius=c0*x ∧ a.childLam=(c0*x)^2 ∧
        a.Z=child.R beta ∧
        a.err=variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
          (n+1) bc hc child.d ((c0*x)^2) ∧
        a.err∈Icc (0:ℝ) (M.context.N^(20*delta)*actualChildErrorBudget (n+1) delta c0 M.context.d M.lam x) := by
  have hsR : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hq := hsR.eventually ((tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop 2))
  filter_upwards [eventually_actual_shell_child_cost_from_target (T:=T) hm hdelta hroom
    hcl hcu hclcu hC0 hc0 hmargin,hq] with n hncost hnq
  intro M x hx hchild1 htarget hweak hmatrix ts epsilon shell hbHist hhHist hlamHist hepsilon
  dsimp only
  intro hregular
  have hcost := hncost M x hx hchild1 htarget hweak hmatrix ts epsilon shell hbHist hhHist hlamHist hepsilon hregular
  obtain ⟨beta,a,hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr⟩ :=
    M.exists_actual_child hc0 hx hmatrix hnq
  refine ⟨beta,a,hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr.1,?_⟩
  rw [he]
  exact hcost

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
