module

public import ComparisonActualHighWallThetaZeroWeakHighOnlyTwoScaleIsolated
public import ComparisonActualHighWallThetaZeroLiteralHighOnlyChildCallDraft
public import ComparisonActualHighWallThetaZeroHighOnlySourceClocks
public import ComparisonActualHighWallSuccessfulChildMinimumAlong
public import ComparisonNativeActualChildDirectCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false

namespace ActualShiftedParentChildCall
theorem bare_clocks_eq_theta_zero_wall
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualShiftedParentChildCall n delta)
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcontext : a.context=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld)
    (hR : a.R=M.data.wallRadius M.alpha) :
    a.childData.b=M.changedBare ∧ a.childData.h=M.changedField := by
  have Hcoef : a.context.coefficient a.alpha=
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha := by
    change omittedStrengthCoefficient a.context.d a.context.s a.R a.context.lam = _
    rw [hR,hcontext]
    rfl
  constructor
  · rw [a.childBareMatrix,Hcoef,hcontext]
    rfl
  · rw [a.childBareField]
    change (fun u => a.context.h u + a.context.coefficient a.alpha u * a.R u) =
      M.changedField
    rw [hR,Hcoef,hcontext]
    rfl
end ActualShiftedParentChildCall

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inverse_radius_le_source_threshold_add_mass_theta_zero
    {n : ℕ} (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.data.wallRadius M.alpha u ≤ Az*M.xs+u/cl := by
  have HR := M.data.wallRadius_bounds M.alpha u
  by_cases hz : M.data.wallRadius M.alpha u ≤ M.z
  · exact (hz.trans M.hzxs).trans (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))
  · have Hz : M.z ≤ M.data.wallRadius M.alpha u := (lt_of_not_ge hz).le
    have Hhigh : M.data.s ≤ u := (M.data.wallRadius_high_mass M.alpha
      (M.hz.1.trans_lt (lt_of_not_ge hz))).le
    have Hreg := (M.regular _ ⟨Hz,HR.2⟩).1
    rw [M.data.wallRadius_spec M.alpha ⟨Hhigh,hu.2⟩] at Hreg
    have H := (le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using Hreg)
    exact H.trans (le_add_of_nonneg_left (mul_nonneg hAz M.hxs.le))

theorem theta_zero_successful_high_only_child_outer_radius_bounds
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→ActualShiftedParentChildCall (dim n+1) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀n,(a n).context=(M n).data.thetaZeroShiftedParentData (M n).lam (M n).hlam (M n).hld)
    (hR : ∀n,(a n).R=(M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).lam) (x n))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d ((M n).lam) (x n)/(x n)^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(M n).data.rmin/x n) atTop (𝓝 0)) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn in atTop,∀u∈Icc (C*x n) 1,
      u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl := by
  let C := max 1 (max (2*cu*Az) (cl*Az))
  have hC : 1 ≤ C := le_max_left _ _
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hClower : 2*cu*Az ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCupper : cl*Az ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  have hcl1 : cl ≤ 1 := by
    have H := ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).1
    simpa only [mul_one,(M 0).alpha.property.2.1] using H
  have Hagree := theta_zero_successful_high_only_child_two_scale_agreement hm hdelta hcl hcu hAz hC0
    hc0 dim hdim M a x hxs hxlim hcontext hR hchild hweak hs hr
  have Hlower := Hagree C (1/2) 1 (1/(4*cu)) (1/4) hCp
    (by norm_num) (by norm_num) (by positivity) (by norm_num)
  have Hupper := Hagree C 1 2 (1/cl) (1/2) hCp zero_lt_one
    (by norm_num) (by positivity) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [Hlower,Hupper] with n hnlo hnup
  intro u hu
  have hup : 0 < u := (mul_pos hCp (hx n)).trans_le hu.1
  have huI : u∈Icc (0:ℝ) 1 := ⟨hup.le,hu.2⟩
  have houter : cu*Az*x n ≤ (1/2)*u := by
    have H := (mul_le_mul_of_nonneg_right hClower (hx n).le).trans hu.1
    nlinarith only [H]
  have HL := hnlo u hu.1 (by simpa only [mul_one] using hu.2)
  have hsizeL : ENNReal.ofReal ((1/4)*u) ≤ volume (Icc (u*(1/2)) (u*1)) := by
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [hup]
  obtain ⟨v,hv,Hv⟩ := exists_pointwise_agreement_of_disagreement_measure_lt
    ((M n).data.wallRadius (M n).alpha) (a n).Z (HL.trans_le hsizeL)
  have hvI : v∈Icc (0:ℝ) 1 :=
    ⟨(by positivity : 0 ≤ u*(1/2)).trans hv.1,by simpa only [mul_one] using hv.2.trans (by simpa only [mul_one] using hu.2)⟩
  have Hrad := (M n).inverse_radius_outer_band_lower_bound_of_parent_scale_theta_zero hcu hAz hvI (hxs n)
    (by simpa only [mul_comm] using hv.1) houter
  change _ ≤ (M n).data.wallRadius (M n).alpha v at Hrad
  have HvZu : (a n).Z v ≤ (a n).Z u := (a n).child_radius_monotone (by simpa only [mul_one] using hv.2)
  have HchildLower : u/(4*cu) ≤ (a n).Z u := by
    have Herr := (abs_le.mp Hv).1
    calc
      u/(4*cu) = (1/2)*u/cu-(1/(4*cu))*u := by field_simp; ring
      _ ≤ (a n).Z v := by linarith only [Hrad,Herr]
      _ ≤ (a n).Z u := HvZu
  refine ⟨HchildLower,?_⟩
  by_cases huHalf : u ≤ 1/2
  · have Hsize : u*2 ≤ 1 := by linarith
    have HU := hnup u hu.1 Hsize
    have hsizeU : ENNReal.ofReal ((1/2)*u) ≤ volume (Icc (u*1) (u*2)) := by
      rw [Real.volume_Icc]
      apply ENNReal.ofReal_le_ofReal
      nlinarith only [hup]
    obtain ⟨v,hv,Hv⟩ := exists_pointwise_agreement_of_disagreement_measure_lt
      ((M n).data.wallRadius (M n).alpha) (a n).Z (HU.trans_le hsizeU)
    have hvI : v∈Icc (0:ℝ) 1 :=
      ⟨by have Hv0 : 0 ≤ u*1 := by simpa only [mul_one] using hup.le
          exact Hv0.trans hv.1, hv.2.trans Hsize⟩
    have HZu : (a n).Z u ≤ (a n).Z v := (a n).child_radius_monotone (by simpa only [mul_one] using hv.1)
    have Hr := (M n).inverse_radius_le_source_threshold_add_mass_theta_zero hcl hAz hvI
    have Hx : Az*(M n).xs ≤ u/cl := by
      have H := (mul_le_mul_of_nonneg_right hCupper (hx n).le).trans hu.1
      apply (le_div_iff₀ hcl).mpr
      have Hxs := mul_le_mul_of_nonneg_left (hxs n) (mul_nonneg hcl.le hAz)
      nlinarith only [H,Hxs]
    have Hdiv : v/cl ≤ (u*2)/cl := div_le_div_of_nonneg_right hv.2 hcl.le
    have Herr := (abs_le.mp Hv).2
    have heq : u/cl+(u*2)/cl+(1/cl)*u=4*u/cl := by ring
    linarith only [HZu,Hr,Hx,Hdiv,Herr,heq]
  · have HZ := ((a n).child_radius_bounds u).2
    apply HZ.trans
    apply (le_div_iff₀ hcl).mpr
    nlinarith only [hcl1,not_le.mp huHalf]

theorem eventually_exists_theta_zero_successful_high_only_child_minimum
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→ActualShiftedParentChildCall (dim n+1) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀n,(a n).context=(M n).data.thetaZeroShiftedParentData (M n).lam (M n).hlam (M n).hld)
    (hR : ∀n,(a n).R=(M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).lam) (x n))
    (hEchild : ∀ᶠn in atTop,(a n).childData.E=actualChildErrorBudget (dim n+1) delta c0
      (M n).data.d ((M n).lam) (x n))
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).data.N delta (M n).data.E
      ((M n).lam) ≤ x n)
    (hT : ∀ᶠn in atTop,(M n).data.T ≤ T)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(M n).data.rmin/x n) atTop (𝓝 0)) :
    ∃C : ℝ,1 ≤ C ∧ Az ≤ 4*C/cl ∧ ∀ᶠn in atTop,
      ∃Q : ActualHighOnlyOverlapMinimum (dim n+1) m delta (cl/4) (4*cu) (4*C/cl) C0 1 1 T,
        Q.data=(a n).childData ∧ Q.lam=(a n).childLam ∧
        HEq Q.optimizer (a n).childOptimizer ∧ Q.xs=x n ∧ Q.z=min ((4*C/cl)*x n) 1 ∧ Q.R=(a n).Z := by
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨Cold,hCold,HquantOld⟩ := theta_zero_successful_high_only_child_outer_radius_bounds hm hdelta hcl hcu hAz hC0
    hc0 dim hdim M a x hxs hxlim hcontext hR hchild hweak hs hr
  let C := max Cold (cl*Az/4)
  have hC : 1 ≤ C := hCold.trans (le_max_left _ _)
  have hAzChild : Az ≤ 4*C/cl := by
    apply (le_div_iff₀ hcl).mpr
    have H : cl*Az/4 ≤ C := le_max_right _ _
    nlinarith only [H]
  have Hquant : ∀ᶠn in atTop,∀u∈Icc (C*x n) 1,u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl := by
    filter_upwards [HquantOld] with n hn
    intro u hu
    exact hn u ⟨(mul_le_mul_of_nonneg_right (le_max_left _ _) (hx n).le).trans hu.1,hu.2⟩
  have hcl1 : cl ≤ 1 := by
    have H := ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).1
    simpa only [mul_one,(M 0).alpha.property.2.1] using H
  have hcu1 : 1 ≤ cu := by
    have H := ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).2
    simpa only [mul_one,(M 0).alpha.property.2.1] using H
  have Hdim : Tendsto (fun n=>dim n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hdim
  have Hgrow := Hdim.eventually (eventually_actual_child_parameters_from_target
    hm hdelta (show 0 < 1/C0 by positivity) hc0 hmargin)
  have Hweak := hweak.eventually (gt_mem_nhds zero_lt_one)
  have Hunit := hxlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨C,hC,hAzChild,?_⟩
  filter_upwards [Hquant,hchild,hEchild,htarget,hT,Hgrow,Hweak,Hunit] with n hnQuant hnChild hnE hnTarget hnT hnGrow hnWeak hnUnit
  have hupper : Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E ≤ (a n).childData.d^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr (M n).data.hN)).mp
      (actual_child_budget_ceiling (dim n+1) delta c0 (M n).data.d ((M n).lam) (x n))
    rw [hnE]
    change _ ≤ (a n).childRadius^2
    rw [hnChild.1]
    simpa only [actualChildRadius,mul_comm] using H
  have hparentlower : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(M n).data.d ≤ (M n).data.E := by
    have H := mul_le_mul_of_nonneg_left (M n).hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hparentupper : (M n).data.E ≤ (M n).data.d^2/Real.sqrt ((dim n+1:ℕ):ℝ) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (M n).data.hN)).mpr
    simpa only [mul_comm] using (M n).hupper
  have hparentweak : laplaceComparisonStrength (M n).data.d (M n).lam (x n) ≤ (x n)^2 :=
    (div_le_one₀ (sq_pos_of_pos (hx n))).mp hnWeak.le
  have Hg := hnGrow (M n).data.d ((M n).lam) (M n).data.E (x n)
    (M n).data.hd (M n).hlam (M n).hld (M n).data.hE (hx n)
    hparentlower hparentupper hnTarget hparentweak
  have hlower : ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).childData.d ≤ C0*(a n).childData.E := by
    have H := mul_le_mul_of_nonneg_left Hg.1 hC0.le
    have hcanc : C0*(1/C0)=1 := by field_simp
    change _*(a n).childRadius ≤ _
    rw [hnChild.1,hnE]
    simpa only [←mul_assoc,hcanc,one_mul,actualChildRadius] using H
  have Hbare := (a n).bare_clocks_eq_theta_zero_wall (M n) (hcontext n) (hR n)
  have htotal : ∀u∈Icc (0:ℝ) 1,(a n).childData.h u+(a n).childData.b u ≤ T := by
    intro u hu
    rw [Hbare.1,Hbare.2]
    exact ((M n).changed_total_clock_le_temperature hu).trans hnT
  have hdD : (a n).childData.d ≤ (1:ℝ) := by
    change (a n).childRadius ≤ 1
    rw [hnChild.1]
    exact (mul_le_mul_of_nonneg_right hc01 (hx n).le).trans (by simpa using hnUnit)
  have hfull : (a n).childLam=(a n).childData.d^2 := by
    change (a n).childLam=(a n).childRadius^2
    rw [hnChild.1]
    exact hnChild.2.1
  let A := (a n).childOptimizer.relam hfull
  have hQuant : ∀u∈Icc (C*x n) 1,u/(4*cu) ≤ (a n).childData.R A.alpha u ∧
      (a n).childData.R A.alpha u ≤ 4*u/cl := by
    simpa only [A,ActualHighOnlyComparisonMinimum.relam_alpha] using hnQuant
  let Q := (a n).childData.successfulChildMinimum hc0 hc01 (hx n) hcl hcu hcl1 hcu1 hC A
    hnChild.1 hdD hupper hlower htotal hQuant
  refine ⟨Q,rfl,?_,?_,rfl,rfl,?_⟩
  · change (a n).childData.d^2=(a n).childLam
    exact hfull.symm
  · change HEq A (a n).childOptimizer
    exact ActualHighOnlyComparisonMinimum.relam_heq _ _
  · change (a n).childData.R A.alpha=(a n).childData.R (a n).childOptimizer.alpha
    rw [ActualHighOnlyComparisonMinimum.relam_alpha]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
