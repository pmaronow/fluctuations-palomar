module

public import ComparisonNativeActualChildDirectCalibration
public import ComparisonNativeActualHistoryChildBudget
public import ComparisonNativeSuccessfulChildFiniteInverseCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem exists_actual_child_attained {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0 < c0) (hx : 0 < x)
    (hroom : M.lam+(c0*x)^2 ≤ M.b 0) (hq : 2 ≤ (n:ℝ)^delta) :
    let c:=M.context.toChildBarrierParameters
    let child:=c.actualChild M.hlam hc0 hx
    ∃β : child.Profile,∃a : NativeChildBarrierCall n delta,
      a.context=c ∧ a.lam=M.lam ∧ HEq a.alpha M.alpha ∧ a.R=M.R ∧ a.b=M.b ∧ a.h=M.h ∧
      a.childRadius=c0*x ∧ a.childLam=(c0*x)^2 ∧ a.Z=child.R β ∧
      a.err=variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM
        n (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
          (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
          child.d ((c0*x)^2) ∧ a.err∈Icc (0:ℝ) ((c0*x)^2) ∧
      variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM
        n (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
          (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
          child.d ((c0*x)^2) β=
      variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM
        n (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
          (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
          child.d ((c0*x)^2) := by
  dsimp only
  let c:=M.context.toChildBarrierParameters
  let child:=c.actualChild M.hlam hc0 hx
  obtain ⟨β,a,hcontext,hlam,halpha,hb,hh,hd,hl,hZ,he,herr,hattained⟩:=
    native_actual_child_call_exists c child M.alpha M.b M.h M.hlam (sq_pos_of_pos (mul_pos hc0 hx))
      M.hb M.hh M.hh0 hroom M.minimum hq
  have hR : a.R=M.R := native_child_radius_eq_of_parent_fields a c M.alpha hcontext halpha
  exact ⟨β,a,hcontext,hlam,halpha,hR,hb,hh,hd,hl,hZ,he,herr,hattained⟩

def actualSuccessfulChildMinimum {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x C T Dchild : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hx : 0 < x)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC : 0 ≤ C)
    (β : (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).Profile)
    (hroom : M.lam+(c0*x)^2 ≤ M.b 0)
    (hattained :
      variableEndpointComparisonSweepObjective
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hc
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hk
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hkc
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hm
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hM
        n (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
          (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
          (c0*x) ((c0*x)^2) β=
      variableEndpointComparisonSweepMinimum
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hc
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hk
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hkc
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hm
        (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).hM
        n (fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u))
          (fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u)
          (c0*x) ((c0*x)^2))
    (hdD : c0*x ≤ Dchild)
    (hlower : (n:ℝ)^(-(2:ℝ)/3+m)*(c0*x) ≤
      C0*actualChildErrorBudget n delta c0 M.context.d M.lam x)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    (hquantile : ∀u∈Icc (C*x) 1,
      u/(4*cu) ≤ (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).R β u ∧
      (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).R β u ≤ 4*u/cl) :
    NativeOverlapMinimum n m delta (cl/4) (4*cu) (4*C/cl) C0 1 Dchild T := by
  let child:=M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx
  let c:=child.toOverlapContext
  let bc:=fun u=>M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)
  let hc:=fun u=>M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u
  have hparent:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
      M.hlb M.hb M.hh M.hh0 M.alpha
  have hbc : MonotoneOn bc (Icc (0:ℝ) 1) := hparent.1
  have hhc : MonotoneOn hc (Icc (0:ℝ) 1) := hparent.2.1
  have hhc0 : 0 ≤ hc 0 := hparent.2.2.2
  have hroom' : (c0*x)^2 ≤ bc 0 := by
    have he:=laplaceComparisonStrength_le M.context.d M.hlam.le (M.R 0)
    dsimp only [bc]; linarith
  have hcl1 : cl ≤ 1 := by
    simpa only [mul_one,M.alpha.property.2] using (M.regular 1 ⟨M.hz.2,le_rfl⟩).1
  have hcu1 : 1 ≤ cu := by
    simpa only [mul_one,M.alpha.property.2] using (M.regular 1 ⟨M.hz.2,le_rfl⟩).2
  have hclcu : cl ≤ cu := hcl1.trans hcu1
  have hinverse := comparison_native_successful_child_inverse_outer_regular
    child.hc child.hk child.hkc child.hm child.hM β hcl hcu hcl1 hclcu hC hx.le hquantile
  have hcal:=actual_child_direct_calibration_at_parent_test (delta:=delta) (d:=M.context.d)
    M.context.hn hc0 hc01 M.hlam hx
  have hupper : Real.sqrt (n:ℝ)*c.E ≤ c.d^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mp
      (actual_child_budget_ceiling n delta c0 M.context.d M.lam x)
    change Real.sqrt (n:ℝ)*actualChildErrorBudget n delta c0 M.context.d M.lam x ≤ (c0*x)^2
    simpa only [actualChildRadius,mul_comm] using H
  have htotal' : ∀u∈Icc (0:ℝ) 1,hc u+bc u ≤ T := by
    intro u hu
    have hR := (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u).2
    have hg := (laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
    have H := mul_le_mul_of_nonneg_left hR hg
    dsimp only [hc,bc]
    linarith [htotal u hu]
  refine {
    context:=c,lam:=(c0*x)^2,hlam:=sq_pos_of_pos (mul_pos hc0 hx),hld:=le_rfl,
    alpha:=β,b:=bc,h:=hc,hb:=hbc,hlb:=hroom',hh:=hhc,hh0:=hhc0,
    minimum:=c.minimum_of_sweep_attained β bc hc (sq_nonneg _) hbc hroom' hhc hhc0 hattained,
    xs:=x,z:=min ((4*C/cl)*x) 1,hxs:=hx,
    hscale:=hcal.1,hz:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩,
    hzxs:=min_le_left _ _,hdD:=hdD,hupper:=hupper,hlower:=hlower,
    htest:=by
      change (n:ℝ)*actualChildErrorBudget n delta c0 M.context.d M.lam x^2 ≤
        1*laplaceComparisonStrength (c0*x) ((c0*x)^2) x*x^2
      simpa only [one_mul,actualChildRadius] using hcal.2.1,
    regular:=?_,clockBudget:=?_ }
  · intro r hr
    by_cases hz1 : (4*C/cl)*x ≤ 1
    · rw [min_eq_left hz1] at hr
      exact hinverse r hr
    · rw [min_eq_right (le_of_not_ge hz1)] at hr
      have hr1 : r=1 := le_antisymm hr.2 hr.1
      subst r
      simpa only [β.property.2,mul_one] using
        And.intro (show cl/4 ≤ 1 by linarith) (show 1 ≤ 4*cu by linarith)
  · have hr := comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM β 1
    have hg := (laplaceComparisonStrength_pos c.d (sq_pos_of_pos (mul_pos hc0 hx)) (c.R β 1)).le
    have hgb := (laplaceComparisonStrength_le c.d (sq_nonneg (c0*x)) (c.R β 1)).trans
      (hroom'.trans (hbc (by norm_num) (by norm_num) zero_le_one))
    have hh1 := hhc0.trans (hhc (by norm_num) (by norm_num) zero_le_one)
    have he := mul_le_mul_of_nonneg_left hr.2 hg
    have hbound : hc 1+laplaceComparisonStrength c.d ((c0*x)^2) (c.R β 1)*c.R β 1 ≤ T := by
      linarith [htotal' 1 (by norm_num)]
    rw [Real.coe_toNNReal _ (add_nonneg hh1 (mul_nonneg hg hr.1))]
    exact (sub_le_self _ (NNReal.coe_nonneg _)).trans hbound

theorem eventually_actual_successful_child_minimum_parameters
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0)
    {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0)) :
    ∀ᶠn in atTop,
      let E:=actualChildErrorBudget (N n+1) delta c0 (M n).context.d (M n).lam (x n)
      let dc:=actualChildRadius c0 (x n)
      Real.sqrt ((N n+1:ℕ):ℝ)*E ≤ dc^2 ∧
      ((N n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*dc ≤ C0*E ∧
      ((N n+1:ℕ):ℝ)^(delta/4)*(M n).context.E ≤ E ∧
      comparisonLowerScale (N n+1) E dc ≤ x n ∧
      ((N n+1:ℕ):ℝ)*E^2 ≤ laplaceComparisonStrength dc (dc^2) (x n)*(x n)^2 ∧
      (x n)^2 ≤ (max 1 (1/c0^3))^2*laplaceComparisonStrength dc (dc^2) (x n) := by
  have hNplus : Tendsto (fun n=>N n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hN
  have Hgrow:=hNplus.eventually (eventually_actual_child_parameters_from_target
    hm hdelta (show 0 < 1/C0 by positivity) hc0 hmargin)
  have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [Hgrow,Hweak,htarget] with n hngrow hnweak hntarget
  dsimp only
  have hnpos := (M n).context.hN
  have hparentupper : (M n).context.E ≤ (M n).context.d^2/Real.sqrt ((N n+1:ℕ):ℝ) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hnpos)).mpr
    simpa only [mul_comm] using (M n).hupper
  have hparentlower : (1/C0)*((N n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(M n).context.d ≤ (M n).context.E := by
    have H:=mul_le_mul_of_nonneg_left (M n).hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hparentweak : laplaceComparisonStrength (M n).context.d (M n).lam (x n) ≤ (x n)^2 := by
    exact (div_le_one₀ (sq_pos_of_pos (hx n))).mp hnweak.le
  have htarget' : ((N n+1:ℕ):ℝ)^delta*Real.sqrt ((N n+1:ℕ):ℝ)*(M n).context.E/
      Real.sqrt (M n).lam ≤ x n := hntarget
  have H:=hngrow (M n).context.d (M n).lam (M n).context.E (x n)
    (M n).context.hd (M n).hlam (M n).hld (M n).context.hE (hx n)
    hparentlower hparentupper htarget' hparentweak
  have hchildlower : ((N n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*actualChildRadius c0 (x n) ≤
      C0*actualChildErrorBudget (N n+1) delta c0 (M n).context.d (M n).lam (x n) := by
    have HH:=mul_le_mul_of_nonneg_left H.1 hC0.le
    have hcanc : C0*(1/C0)=1 := by field_simp
    simpa only [←mul_assoc,hcanc,one_mul] using HH
  have hchildupper : Real.sqrt ((N n+1:ℕ):ℝ)*
      actualChildErrorBudget (N n+1) delta c0 (M n).context.d (M n).lam (x n) ≤
      (actualChildRadius c0 (x n))^2 := by
    have HH:=(le_div_iff₀ (Real.sqrt_pos.mpr hnpos)).mp H.2.1
    simpa only [mul_comm] using HH
  have Hcal:=actual_child_direct_calibration_at_parent_test (delta:=delta) (d:=(M n).context.d)
    (M n).context.hn hc0 hc01 (M n).hlam (hx n)
  exact ⟨hchildupper,hchildlower,H.2.2.1,by
    simpa only [Nat.cast_add,Nat.cast_one] using Hcal⟩

theorem actual_successful_child_terminal_quantile {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x x0 : ℝ} (hc0 : 0 < c0) (hx : 0 < x) (hx0 : 0 < x0) (hxx0 : x0 ≤ x)
    (β : (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).Profile) :
    ∀u∈Icc ((2/x0)*x) 1,
      u/(4*cu) ≤ (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).R β u ∧
      (M.context.toChildBarrierParameters.actualChild M.hlam hc0 hx).R β u ≤ 4*u/cl := by
  intro u hu
  have H := mul_le_mul_of_nonneg_left hxx0 (show 0 ≤ 2/x0 by positivity)
  have he : (2/x0)*x0=2 := div_mul_cancel₀ _ hx0.ne'
  rw [he] at H
  linarith only [H,hu.1,hu.2]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
