module

public import ComparisonNativeActualSelectedBadChild
public import ComparisonNativeActualRegularConditionalDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
theorem eventually_actual_regular_sweep_density_of_regular
    {margin delta cl cu C0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀(c : NativeOverlapContext (n+1) delta) (alpha : c.Profile)
        (b h : ℝ→ℝ) (lam : ℝ),
      0 < lam → lam ≤ c.d^2 → c.d ≤ 1 → lam ≤ b 0 →
      MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) → 0 ≤ h 0 →
      Real.sqrt c.N*c.E ≤ c.d^2 → c.N^(-(2:ℝ)/3+margin)*c.d ≤ C0*c.E →
      variableEndpointComparisonSweepObjective c.hc c.hk c.hkc c.hm c.hM (n+1) b h c.d lam alpha=
        variableEndpointComparisonSweepMinimum c.hc c.hk c.hkc c.hm c.hM (n+1) b h c.d lam →
      (∀r∈Icc (min (comparisonConditionalScale c.N delta c.E lam) 1) 1,
        cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      NativePullbackClockRegularity alpha.val.val b h 0 1 →
      (∀u∈Icc (0:ℝ) 1,h u+b u ≤ T) →
      nativeActualSweepDensity c.hc c.hk c.hkc c.hm c.hM (n+1) b h c.d lam alpha ≤
        c.N^(10*delta)*c.E := by
  have hevent := NativeOverlapMinimum.eventually_actual_regular_conditional_density
    (Az:=1) (Ct:=1) (D:=1) (Bclock:=T) hm hdelta hroom hcl hcu hclcu
    (by norm_num) hC0 (by norm_num)
  filter_upwards [hevent] with n hn
  intro c alpha b h lam hlam hld hd1 hlb hb hh hh0 hupper hlower hattained hregular
    hclock htotal'
  have hminimum := c.minimum_of_sweep_attained alpha b h hlam.le hb hlb hh hh0 hattained
  let a := c.conditionalMinimum alpha b h hlam hld hdelta.le hb hlb hh hh0 hminimum hd1
    hupper hlower htotal' hregular
  exact hn a hd1 rfl hclock

theorem eventually_actual_regular_child_cost_of_regular
    {margin delta cl cu C0 T : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀(child : NativeChildBarrierParameters (n+1) delta) (b h : ℝ→ℝ) (L : ℝ),
      0 < L → L ≤ child.d^2 → child.d ≤ 1 → L ≤ b 0 →
      MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) → 0 ≤ h 0 →
      Real.sqrt child.N*child.E ≤ child.d^2 →
      child.N^(-(2:ℝ)/3+margin)*child.d ≤ C0*child.E →
      (∀alpha : child.Profile,NativePullbackClockRegularity alpha.val.val b h 0 1) →
      (∀u∈Icc (0:ℝ) 1,h u+b u ≤ T) →
      (∀lam∈Ioo (child.N^(-10:ℝ)) L,∀alpha : child.Profile,
        variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
          (n+1) b h child.d lam alpha=
          variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
            (n+1) b h child.d lam →
        ∀r∈Icc (min (comparisonConditionalScale child.N delta child.E lam) 1) 1,
          cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
        (n+1) b h child.d L ≤ child.N^(20*delta)*child.E := by
  have hgamma : 0 < 1/C0 := one_div_pos.mpr hC0
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsR : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
  have hq := hsR.eventually ((tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop 2))
  filter_upwards [eventually_actual_regular_sweep_density_of_regular (T:=T) hm hdelta hroom
    hcl hcu hclcu hC0,hs.eventually (eventually_native_actual_child_cost_of_density hm hdelta hgamma),hq]
    with n hndensity hncost hnq
  intro child b h L hL hLd hd1 hLb hb hh hh0 hupper hlower hclock htotal hregular
  have hL1 : L ≤ 1 := by have hd:=child.hd; nlinarith
  have hup : child.E ≤ child.d^2/Real.sqrt (n+1:ℕ) := by
    exact (le_div_iff₀ (Real.sqrt_pos.mpr child.hN)).mpr (by simpa only [mul_comm] using hupper)
  have hlo : (1/C0)*child.N^(-(2:ℝ)/3+margin)*child.d ≤ child.E := by
    have hh := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
  apply hncost child b h L hL hL1 hLb hb hh hh0 hlo hup hnq
  intro lam hlam alpha hattained
  have hlam0 : 0 < lam := (Real.rpow_pos_of_pos child.hN _).trans hlam.1
  exact hndensity child.toOverlapContext alpha b h lam hlam0 (hlam.2.le.trans hLd) hd1
    (hlam.2.le.trans hLb) hb hh hh0 hupper hlower hattained (hregular lam hlam alpha hattained)
    (hclock alpha) htotal

namespace NativeOverlapMinimum
theorem eventually_actual_regular_child_cost_from_target
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
      (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) →
      let child := M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
      let bc := fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
      let hc := fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
      (∀alpha : child.Profile,NativePullbackClockRegularity alpha.val.val bc hc 0 1) →
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
  filter_upwards [eventually_actual_regular_child_cost_of_regular (T:=T) hm hdelta hroom hcl hcu hclcu hC0,
    hs.eventually (eventually_actual_child_parameters_from_target hm hdelta hgamma hc0 hmargin)]
    with n hncost hnparams
  intro M x hx hchild1 htarget hweak hmatrix htotalParent
  dsimp only
  intro hclock hregular
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
  have htotalChild : ∀u∈Icc (0:ℝ) 1,hc u+bc u ≤ T := by
    intro u hu
    have H:=htotalParent u hu
    have HR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u
    have Hg:=(laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
    have Hmul:=mul_le_mul_of_nonneg_left HR.2 Hg
    dsimp only [bc,hc]
    linarith only [H,Hmul]
  exact hncost child bc hc ((c0*x)^2) (sq_pos_of_pos (mul_pos hc0 hx)) le_rfl hchild1 hroom'
    had.1 had.2.1 had.2.2.2 hchildUpper hchildLower
    hclock htotalChild hregular

theorem eventually_actual_regular_child_failure_from_target
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
      (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) →
      let child := M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
      let bc := fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
      let hc := fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
      (∀alpha : child.Profile,NativePullbackClockRegularity alpha.val.val bc hc 0 1) →
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
  filter_upwards [eventually_actual_regular_child_cost_from_target (T:=T) hm hdelta hroom
    hcl hcu hclcu hC0 hc0 hmargin] with n hn
  intro M x hx hchild1 htarget hweak hmatrix htotalParent
  dsimp only
  intro hclock hfail
  by_contra hno
  push Not at hno
  have hcost:=hn M x hx hchild1 htarget hweak hmatrix htotalParent hclock (by
      intro lam hlam alpha hattained r hr
      exact hno lam hlam alpha hattained r hr)
  exact not_lt_of_ge hcost hfail

theorem eventually_exists_actual_selected_bad_regular_child_from_target
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
      (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) →
      let child:=M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
      let bc:=fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
      let hc:=fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
      (∀alpha : child.Profile,NativePullbackClockRegularity alpha.val.val bc hc 0 1) →
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
          (Q.alpha.val.val Q.xs < cl*Q.xs ∨ cu*Q.xs < Q.alpha.val.val Q.xs) := by
  have hcu : 0 < cu:=zero_lt_one.trans_le hcu1
  have hclcu : cl ≤ cu:=hcl1.trans hcu1
  have hgamma : 0 < 1/C0:=one_div_pos.mpr hC0
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [eventually_actual_regular_child_failure_from_target (Bclock:=T) (T:=T)
    hm hdelta hroom hcl hcu hclcu hC0 hc0 hmargin,
    hs.eventually (eventually_actual_child_parameters_from_target hm hdelta hgamma hc0 hmargin)]
    with n hnFailure hnParams
  intro M x hx hchild1 hchildD htarget hweak hmatrix htotalParent
  dsimp only
  intro hclock hfail
  let child:=M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
  let bc:=fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
  let hc:=fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
  obtain ⟨lam,hlam,alpha,hattained,hbad⟩:=hnFailure M x hx hchild1 htarget hweak hmatrix
    htotalParent hclock hfail
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
  have htotal : ∀u∈Icc (0:ℝ) 1,hc u+bc u ≤ T := by
    intro u hu
    have H:=htotalParent u hu
    have HR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u
    have Hg:=(laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
    have Hmul:=mul_le_mul_of_nonneg_left HR.2 Hg
    dsimp only [bc,hc]
    linarith only [H,Hmul]
  have hlam0 : 0 < lam:=(Real.rpow_pos_of_pos child.hN _).trans hlam.1
  have hld : lam ≤ child.toOverlapContext.d^2:=hlam.2.le
  obtain ⟨Q,hcontext,hQlam,hAlpha,hbQ,hhQ,hRQ,hxs,hz,hbadQ⟩:=
    child.toOverlapContext.exists_selected_bad_scale_minimum_of_attained alpha bc hc
      hlam0 hld hdelta.le had.1 (hlam.2.le.trans hroomChild) had.2.1 had.2.2.2 hattained
      hchildD hchildUpper hchildLower htotal hAz hCt hcl1 hcu1 hbad
  refine ⟨lam,hlam,alpha,hattained,Q,hcontext,hQlam,hAlpha,hbQ,hhQ,hRQ,?_,?_,?_,hxs,hz,hbadQ⟩
  · rw [hcontext]
    rfl
  · rw [hcontext]
    rfl
  · rw [hcontext]
    exact hp.2.2.1
end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
