module

public import ComparisonActualHighWallSuccessfulChildMinimumAlong
public import ComparisonActualHighWallSuccessfulAllMassChildOuterRadiusBounds
public import ComparisonActualShiftedAllMassZeroDataBridge
public import ComparisonActualHighWallOriginsAlong

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ActualShiftedAllMassParentChildCall
theorem bare_clocks_eq_actual_wall
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualShiftedAllMassParentChildCall n delta)
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcontext : a.context=M.data.shiftedParentData)
    (hR : a.R=M.data.wallRadius M.alpha) :
    (fun u=>a.context.b u-a.coefficient u)=M.data.b M.alpha ∧
      (fun u=>a.context.h u+a.coefficient u*a.R u)=M.data.h M.alpha := by
  have Hcoef : a.context.coefficient a.alpha=
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) := by
    change omittedStrengthCoefficient a.context.d a.context.s a.R a.context.lam=_
    rw [hR,hcontext]
    rfl
  constructor
  · change (fun u=>a.context.b u-a.context.coefficient a.alpha u)=M.data.b M.alpha
    rw [Hcoef,hcontext,M.data.masked_coefficient_eq M.alpha]
    rfl
  · change (fun u=>a.context.h u+a.context.coefficient a.alpha u*a.R u)=M.data.h M.alpha
    rw [Hcoef]
    rw [hR,hcontext]
    ext u
    change wallBareField M.data.T M.data.epsilon M.data.theta M.data.s M.data.tau M.data.d M.data.rmin u+
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u*
        M.data.wallRadius M.alpha u=M.data.h M.alpha u
    rw [congrFun (M.data.masked_field_coefficient_eq M.alpha) u]
    rfl

end ActualShiftedAllMassParentChildCall
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}
theorem eventually_exists_successful_all_mass_child_minimum
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→ActualShiftedAllMassParentChildCall (dim n+1) delta)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀n,(a n).context=(M n).data.shiftedParentData)
    (hR : ∀n,(a n).R=(M n).data.wallRadius (M n).alpha)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n))
    (hEchild : ∀ᶠn in atTop,(a n).childData.E=actualChildErrorBudget (dim n+1) delta c0
      (M n).data.d ((M n).data.d^2) (x n))
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).data.N delta (M n).data.E
      ((M n).data.d^2) ≤ x n)
    (hT : ∀ᶠn in atTop,(M n).data.T ≤ T)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d ((M n).data.d^2) (x n)/(x n)^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(M n).data.rmin/x n) atTop (𝓝 0)) :
    ∃C : ℝ,1 ≤ C ∧ Az ≤ 4*C/cl ∧ ∀ᶠn in atTop,
      ∃Q : ActualHighOnlyOverlapMinimum (dim n+1) m delta (cl/4) (4*cu) (4*C/cl) C0 1 1 T,
        Q.data.E=(a n).childData.E ∧ Q.data.d=(a n).childRadius ∧ Q.data.s=0 ∧
        Q.data.b=(M n).data.b (M n).alpha ∧ Q.data.h=(M n).data.h (M n).alpha ∧
        Q.lam=(a n).childLam ∧ HEq Q.alpha (a n).childAlpha ∧
        Q.xs=x n ∧ Q.z=min ((4*C/cl)*x n) 1 ∧ Q.R=(a n).Z := by
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨Cold,hCold,HquantOld⟩ := successful_all_mass_child_outer_radius_bounds hm hdelta hcl hcu hAz hC0
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
  have hupper : Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E ≤ (a n).childRadius^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr (M n).data.hN)).mp
      (actual_child_budget_ceiling (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n))
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
  have hparentweak : laplaceComparisonStrength (M n).data.d ((M n).data.d^2) (x n) ≤ (x n)^2 :=
    (div_le_one₀ (sq_pos_of_pos (hx n))).mp hnWeak.le
  have Hg := hnGrow (M n).data.d ((M n).data.d^2) (M n).data.E (x n)
    (M n).data.hd (sq_pos_of_pos (M n).data.hd) le_rfl (M n).data.hE (hx n)
    hparentlower hparentupper hnTarget hparentweak
  have hlower : ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).childRadius ≤ C0*(a n).childData.E := by
    have H := mul_le_mul_of_nonneg_left Hg.1 hC0.le
    have hcanc : C0*(1/C0)=1 := by field_simp
    change _*(a n).childRadius ≤ _
    rw [hnChild.1,hnE]
    simpa only [←mul_assoc,hcanc,one_mul,actualChildRadius] using H
  have Hbare := (a n).bare_clocks_eq_actual_wall (M n) (hcontext n) (hR n)
  have htotal : ∀u∈Icc (0:ℝ) 1,
      ((a n).context.h u+(a n).coefficient u*(a n).R u)+
      ((a n).context.b u-(a n).coefficient u) ≤ T := by
    intro u hu
    change (fun u=>(a n).context.h u+(a n).coefficient u*(a n).R u) u+
      (fun u=>(a n).context.b u-(a n).coefficient u) u ≤ T
    rw [Hbare.1,Hbare.2]
    have H := (M n).data.total_clock_le (M n).alpha u hu
    rw [((M n).data.clock_coe (M n).alpha hu).1,((M n).data.clock_coe (M n).alpha hu).2] at H
    exact H.trans hnT
  have hdD : (a n).childRadius ≤ (1:ℝ) := by
    rw [hnChild.1]
    exact (mul_le_mul_of_nonneg_right hc01 (hx n).le).trans (by simpa using hnUnit)
  have hfull : (a n).childLam=(a n).childRadius^2 := by
    rw [hnChild.1]
    exact hnChild.2.1
  have hroom : (a n).childRadius^2 ≤ (a n).context.b 0-(a n).coefficient 0 := by
    rw [←hfull]
    exact (a n).matrixRoom
  let data := (a n).zeroMassData (M n).data.hq hroom
  let A := ((a n).zeroMassMinimum (M n).data.hq hroom).relam hfull
  have hQuant : ∀u∈Icc (C*x n) 1,u/(4*cu) ≤ data.R A.alpha u ∧ data.R A.alpha u ≤ 4*u/cl := by
    intro u hu
    dsimp only [A]
    rw [ActualHighOnlyComparisonMinimum.relam_alpha]
    change u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl
    exact hnQuant u hu
  let Q := data.successfulChildMinimum hc0 hc01 (hx n) hcl hcu hcl1 hcu1 hC A
    hnChild.1 hdD hupper hlower htotal hQuant
  refine ⟨Q,rfl,rfl,rfl,?_,?_,?_,?_,rfl,rfl,?_⟩
  · change (fun u=>(a n).context.b u-(a n).coefficient u)=(M n).data.b (M n).alpha
    exact Hbare.1
  · change (fun u=>(a n).context.h u+(a n).coefficient u*(a n).R u)=(M n).data.h (M n).alpha
    exact Hbare.2
  · change (a n).childRadius^2=(a n).childLam
    exact hfull.symm
  · change HEq A.alpha (a n).childAlpha
    dsimp only [A]
    rw [ActualHighOnlyComparisonMinimum.relam_alpha]
    rfl
  · change data.R A.alpha=(a n).Z
    dsimp only [A]
    rw [ActualHighOnlyComparisonMinimum.relam_alpha]
    rfl

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
