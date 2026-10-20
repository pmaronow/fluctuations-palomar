module

public import ComparisonActualHighOnlyClocks
public import ComparisonNativeActualChildClockIncrementProducer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem eventually_actual_child_clock_increments_from_target
    (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    {eta C : ℝ} (heta : 0 < eta) (heta1 : eta ≤ 1) (hC : 1 ≤ C)
    (hmargin : 0 < 9*m-298*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(P : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      x∈Ioc (0:ℝ) 1 → comparisonConditionalScale P.context.N delta P.context.E P.lam ≤ x →
      laplaceComparisonStrength P.context.d P.lam x ≤ (eta*c0)^3*x^2 →
      ∀r∈Icc (0:ℝ) 1,r ≤ C*x →
        laplaceComparisonStrength P.context.d P.lam r ≤
          eta^2*(actualChildCutoff (n+1) delta c0 P.context.d P.lam x)^2 ∧
        laplaceComparisonStrength P.context.d P.lam r*r ≤
          C*eta^3*(actualChildCutoff (n+1) delta c0 P.context.d P.lam x)^3 := by
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  have H:=actual_child_nonceiling_clocks_eventually m delta c0 1 (1/C0) eta C hc0 hc01
    zero_lt_one (one_div_pos.mpr hC0) heta heta1 hC hmargin
  filter_upwards [hs.eventually H] with n hn
  intro P x hx htarget hweak r hr hrC
  have hlo : (1/C0)*P.context.N^(-(2:ℝ)/3+m)*P.context.d ≤ P.context.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using P.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : P.context.E ≤ P.context.d^2/Real.sqrt (n+1:ℕ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr P.context.hN)).mpr (by simpa only [mul_comm] using P.hupper)
  have hax : Real.sqrt (n+1:ℕ)*P.context.E/P.context.d ≤ x :=
    (comparison_conditional_scale_ge_lower (by exact_mod_cast P.context.hn) hdelta.le
      P.context.hE P.context.hd P.hlam P.hld).trans htarget
  have hdirect : ((n+1:ℕ):ℝ)^(1+delta)*P.context.E^2 ≤
      laplaceComparisonStrength P.context.d P.lam x*x^2 := by
    have H:=comparison_radius_target_strength_size (by exact_mod_cast P.context.hn)
      hdelta.le P.context.hd P.hlam P.hld P.context.hE hup hx.1
      (C:=1) le_rfl hx.1 (by simp) htarget
    have he : P.context.N^(1+delta)=P.context.N^delta*P.context.N := by
      rw [show (1:ℝ)+delta=delta+1 by ring,Real.rpow_add P.context.hN,Real.rpow_one]
    simpa only [div_one,he] using H
  by_cases Hcase : (actualChildRadius c0 x)^2/Real.sqrt (n+1:ℕ) ≤
      ((n+1:ℕ):ℝ)^(-100*delta)*laplaceComparisonStrength P.context.d P.lam x*x^3
  · have ha : actualChildCutoff (n+1) delta c0 P.context.d P.lam x=c0*x := by
      unfold actualChildCutoff actualChildErrorBudget
      rw [min_eq_left Hcase]
      unfold actualChildRadius
      field_simp
    rw [ha]
    have hgap : laplaceComparisonStrength P.context.d P.lam x*x ≤ eta^3*(c0*x)^3 := by
      have H:=mul_le_mul_of_nonneg_right hweak hx.1.le
      nlinarith only [H]
    exact actual_child_clock_increments P.context.hd P.hlam P.hld hx (mul_pos hc0 hx.1)
      (mul_le_of_le_one_left hx.1.le hc01) heta.le heta1 hgap hC hr hrC
  · have hbudget : actualChildErrorBudget (n+1) delta c0 P.context.d P.lam x=
        ((n+1:ℕ):ℝ)^(-100*delta)*laplaceComparisonStrength P.context.d P.lam x*x^3 :=
      min_eq_right (le_of_not_ge Hcase)
    exact hn P.context.d P.lam x P.context.E P.context.hd P.hlam P.hld hx hlo hup hax
      (by simpa only [one_mul] using hdirect) hbudget r hr hrC

theorem eventually_actual_child_positive_band_increments
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) {eta Cmass : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hCmass : 0 ≤ Cmass)
    (hmargin : 0 < 9*m-298*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(P : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      x∈Ioc (0:ℝ) 1 → comparisonConditionalScale P.context.N delta P.context.E P.lam ≤ x →
      laplaceComparisonStrength P.context.d P.lam x ≤ (eta*c0)^3*x^2 → P.z ≤ Az*x →
      ∀y : ℝ,actualChildCutoff (n+1) delta c0 P.context.d P.lam x ≤ y →
      ∀u∈Icc (0:ℝ) (min (Cmass*y) 1),
        laplaceComparisonStrength P.context.d P.lam (P.R u) ≤ eta^2*y^2 ∧
        laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u ≤
          max 1 (Az+Cmass/cl)*eta^2*y^3 := by
  let C:=max 1 (Az+Cmass/cl)
  have hC : 1 ≤ C:=le_max_left _ _
  have hC0' : 0 ≤ C:=zero_le_one.trans hC
  filter_upwards [eventually_actual_child_clock_increments_from_target
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hdelta hC0 hc0 hc01 heta heta1 hC hmargin] with n hn
  intro P x hx htarget hweak hz y hay u hu
  let a:=actualChildCutoff (n+1) delta c0 P.context.d P.lam x
  have ha : 0 < a:=(actual_child_cutoff_pos_le_radius P.context.hN hc0 P.hlam hx.1).1
  have hy : 0 < y:=ha.trans_le hay
  have hu1 : u∈Icc (0:ℝ) 1:=⟨hu.1,hu.2.trans (min_le_right _ _)⟩
  have huCy : u ≤ Cmass*y:=hu.2.trans (min_le_left _ _)
  have hr:=omittedSweepQuantile_bounds zero_le_one ⟨P.data.hs.1,P.data.hs1⟩
    P.context.hc P.context.hk P.context.hkc P.context.hm P.context.hM P.alpha u
  have Hzero:=hn P x hx htarget hweak 0 (by norm_num) (mul_nonneg hC0' hx.1.le)
  have hlam : P.lam ≤ eta^2*a^2 := by
    simpa only [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape,
      mul_zero,zero_div,ite_eq_left (by norm_num : (0:ℝ) ≤ 1),mul_one] using Hzero.1
  have Hg : laplaceComparisonStrength P.context.d P.lam (P.R u) ≤ eta^2*y^2 :=
    (laplaceComparisonStrength_le P.context.d P.hlam.le _).trans
      (hlam.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hay 2) (sq_nonneg eta)))
  refine ⟨Hg,?_⟩
  have Hr : P.R u ≤ Az*x+(Cmass/cl)*y := by
    have H:=P.inverse_radius_le_regular_cap hcl hu1
    have Hdiv : u/cl ≤ (Cmass/cl)*y := by
      convert div_le_div_of_nonneg_right huCy hcl.le using 1
      ring
    linarith only [H,Hdiv,hz]
  by_cases hyx : y ≤ x
  · have HrCx : P.R u ≤ C*x := by
      have H:=mul_le_mul_of_nonneg_left hyx (div_nonneg hCmass hcl.le)
      have H':=mul_le_mul_of_nonneg_right (le_max_right 1 (Az+Cmass/cl)) hx.1.le
      nlinarith only [Hr,H,H']
    have HH:=(hn P x hx htarget hweak (P.R u) hr HrCx).2
    have Hpow:=pow_le_pow_left₀ ha.le hay 3
    have Het : eta^3 ≤ eta^2 := by
      have H:=mul_le_mul_of_nonneg_left heta1 (sq_nonneg eta)
      nlinarith only [H]
    have H1:=mul_le_mul_of_nonneg_left Hpow (mul_nonneg hC0' (pow_nonneg heta.le 3))
    have H2:=mul_le_mul_of_nonneg_left Het (mul_nonneg hC0' (pow_nonneg hy.le 3))
    change laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u ≤ C*eta^2*y^3
    nlinarith only [HH,H1,H2]
  · have HrCy : P.R u ≤ C*y := by
      have H:=mul_le_mul_of_nonneg_left (le_of_not_ge hyx) hAz
      have H':=mul_le_mul_of_nonneg_right (le_max_right 1 (Az+Cmass/cl)) hy.le
      nlinarith only [Hr,H,H']
    have H:=mul_le_mul Hg HrCy hr.1 (by positivity : 0 ≤ eta^2*y^2)
    change laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u ≤ C*eta^2*y^3
    nlinarith only [H]

theorem actual_child_positive_band_increments_vanish_of_call_bounded
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hmargin : 0 < 9*m-298*delta)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (P : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam ≤ x n)
    (hcap : ∀ᶠn in atTop,(P n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
      atTop (𝓝 0)) :
    ∀Cmass epsilon : ℝ,0 ≤ Cmass → 0 < epsilon → ∀ᶠn in atTop,
      ∀y : ℝ,actualChildCutoff (N n+1) delta c0 (P n).context.d (P n).lam (x n) ≤ y →
      ∀u∈Icc (0:ℝ) (min (Cmass*y) 1),
        laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u) ≤ epsilon*y^2 ∧
        laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u ≤ epsilon*y^3 := by
  intro Cmass epsilon hCmass heps
  let C:=max 1 (Az+Cmass/cl)
  let eta:=min 1 (epsilon/(C+1))
  have hC : 1 ≤ C:=le_max_left _ _
  have hC0' : 0 ≤ C:=zero_le_one.trans hC
  have heta : 0 < eta:=lt_min zero_lt_one (div_pos heps (by positivity))
  have heta1 : eta ≤ 1:=min_le_left _ _
  have Het : eta*(C+1) ≤ epsilon:=
    (le_div_iff₀ (by positivity : 0 < C+1)).mp (min_le_right _ _)
  have Het2 : eta^2 ≤ eta := by nlinarith
  have hsave : eta^2 ≤ epsilon ∧ C*eta^2 ≤ epsilon := by
    have H:=mul_le_mul_of_nonneg_left Het2 hC0'
    constructor <;> nlinarith only [Het,Het2,H,heta.le,hC,mul_nonneg heta.le hC0']
  have Hweak:=hweak.eventually (gt_mem_nhds (pow_pos (mul_pos heta hc0) 3))
  filter_upwards [hN.eventually (eventually_actual_child_positive_band_increments (cu:=cu) (Ct:=Ct)
    (D:=D) (Bclock:=Bclock) hdelta hcl hAz hC0 hc0 hc01 heta heta1 hCmass hmargin),
    Hweak,hxunit,htarget,hcap] with n hn hnweak hnunit hntarget hncap
  intro y hay u hu
  have Hweak' : laplaceComparisonStrength (P n).context.d (P n).lam (x n) ≤ (eta*c0)^3*(x n)^2 :=
    (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le
  have H:=hn (P n) (x n) ⟨hx n,hnunit⟩ hntarget Hweak' hncap y hay u hu
  have hy : 0 < y:=
    (actual_child_cutoff_pos_le_radius (P n).context.hN hc0 (P n).hlam (hx n)).1.trans_le hay
  exact ⟨H.1.trans (mul_le_mul_of_nonneg_right hsave.1 (sq_nonneg y)),
    H.2.trans (mul_le_mul_of_nonneg_right hsave.2 (pow_nonneg hy.le 3))⟩

theorem eventually_actual_parent_cap_and_cutoff_inherit
    (hm : 0 < m) (hdelta : 0<delta) (hAz : 0≤Az) (hC0 : 0<C0) (hc0 : 0<c0)
    (hmargin : delta/4<3*m-99*delta) (hcapmargin : 100*delta<(1:ℝ)/3+m) :
    ∀ᶠn : ℕ in atTop,
      ∀(P M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      0<x → comparisonConditionalScale P.context.N delta P.context.E P.lam≤x →
      laplaceComparisonStrength P.context.d P.lam x≤x^2 → P.z≤Az*x →
      M.context.d=actualChildRadius c0 x →
      M.context.E=actualChildErrorBudget (n+1) delta c0 P.context.d P.lam x →
      P.lam*P.z≤(Az*max 1 (D^2/c0))*comparisonLowerScale M.context.N M.context.E M.context.d ∧
      comparisonLowerScale P.context.N P.context.E P.context.d≤
        comparisonLowerScale M.context.N M.context.E M.context.d := by
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop:=tendsto_add_atTop_nat 1
  filter_upwards [hs.eventually (eventually_actual_parent_strength_radius_le_child_cutoff
    (D:=D) (one_div_pos.mpr hC0) hc0 hcapmargin),
    hs.eventually (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)] with n hncap hnchild
  intro P M x hx htarget hweak hz hd hE
  have hlo : (1/C0)*P.context.N^(-(2:ℝ)/3+m)*P.context.d≤P.context.E := by
    have H:=(div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using P.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : P.context.E≤P.context.d^2/Real.sqrt (n+1:ℕ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr P.context.hN)).mpr (by simpa only [mul_comm] using P.hupper)
  have hax : comparisonLowerScale P.context.N P.context.E P.context.d≤x :=
    (comparison_conditional_scale_ge_lower (by exact_mod_cast P.context.hn) hdelta.le
      P.context.hE P.context.hd P.hlam P.hld).trans htarget
  have Hcap:=hncap P.context.d P.lam P.context.E x P.context.hd P.hlam P.hld P.hdD hx hlo hup hax
  have Hchild:=hnchild P.context.d P.lam P.context.E x P.context.hd P.hlam P.hld
    P.context.hE hx hlo hup htarget hweak
  have heq : comparisonLowerScale M.context.N M.context.E M.context.d=
      actualChildCutoff (n+1) delta c0 P.context.d P.lam x := by
    unfold comparisonLowerScale actualChildCutoff
    rw [hE,hd]
  rw [heq]
  constructor
  · have H1:=mul_le_mul_of_nonneg_left hz P.hlam.le
    have H2:=mul_le_mul_of_nonneg_left Hcap hAz
    nlinarith only [H1,H2]
  · exact Hchild.2.2.2.1

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
