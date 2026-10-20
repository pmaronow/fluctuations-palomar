module

public import ComparisonActualHighOnlySuccessfulChildMinimum
public import ComparisonActualHighWallSuccessfulChildOuterRadiusBounds
public import ComparisonActualHighWallOriginsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ActualHighOnlyComparisonMinimum
variable {n : ℕ} {delta lam lam' : ℝ} {a : ActualHighOnlyComparisonData n delta}
def relam (Q : ActualHighOnlyComparisonMinimum a lam) (h : lam=lam') :
    ActualHighOnlyComparisonMinimum a lam' := h ▸ Q

theorem relam_heq (Q : ActualHighOnlyComparisonMinimum a lam) (h : lam=lam') :
    HEq (Q.relam h) Q := by
  cases h
  rfl

theorem relam_alpha (Q : ActualHighOnlyComparisonMinimum a lam) (h : lam=lam') :
    (Q.relam h).alpha=Q.alpha := by
  cases h
  rfl
end ActualHighOnlyComparisonMinimum

namespace ActualShiftedParentChildCall

theorem bare_clocks_eq_actual_wall
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualShiftedParentChildCall n delta)
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcontext : a.context=M.data.shiftedParentData)
    (hR : a.R=M.data.wallRadius M.alpha) :
    a.childData.b=M.data.b M.alpha ∧ a.childData.h=M.data.h M.alpha := by
  have Hcoef : a.context.coefficient a.alpha=
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) := by
    change omittedStrengthCoefficient a.context.d a.context.s a.R a.context.lam=_
    rw [hR,hcontext]
    rfl
  constructor
  · rw [a.childBareMatrix,Hcoef,hcontext,M.data.masked_coefficient_eq M.alpha]
    rfl
  · rw [a.childBareField,Hcoef]
    change (fun u=>a.context.h u+
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u*a.R u)=M.data.h M.alpha
    rw [hR,hcontext]
    ext u
    change wallBareField M.data.T M.data.epsilon M.data.theta M.data.s M.data.tau M.data.d M.data.rmin u+
      omittedStrengthCoefficient M.data.d M.data.s (M.data.wallRadius M.alpha) (M.data.d^2) u*
        M.data.wallRadius M.alpha u=M.data.h M.alpha u
    rw [congrFun (M.data.masked_field_coefficient_eq M.alpha) u]
    rfl

end ActualShiftedParentChildCall

namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem eventually_exists_successful_high_only_child_minimum
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ)→ActualShiftedParentChildCall (dim n+1) delta)
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
        Q.data=(a n).childData ∧ Q.lam=(a n).childLam ∧
        HEq Q.optimizer (a n).childOptimizer ∧ Q.xs=x n ∧ Q.z=min ((4*C/cl)*x n) 1 ∧ Q.R=(a n).Z := by
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  obtain ⟨Cold,hCold,HquantOld⟩ := successful_high_only_child_outer_radius_bounds hm hdelta hcl hcu hAz hC0
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
  have hlower : ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a n).childData.d ≤ C0*(a n).childData.E := by
    have H := mul_le_mul_of_nonneg_left Hg.1 hC0.le
    have hcanc : C0*(1/C0)=1 := by field_simp
    change _*(a n).childRadius ≤ _
    rw [hnChild.1,hnE]
    simpa only [←mul_assoc,hcanc,one_mul,actualChildRadius] using H
  have Hbare := (a n).bare_clocks_eq_actual_wall (M n) (hcontext n) (hR n)
  have htotal : ∀u∈Icc (0:ℝ) 1,(a n).childData.h u+(a n).childData.b u ≤ T := by
    intro u hu
    rw [Hbare.1,Hbare.2]
    have H := (M n).data.total_clock_le (M n).alpha u hu
    rw [((M n).data.clock_coe (M n).alpha hu).1,((M n).data.clock_coe (M n).alpha hu).2] at H
    exact H.trans hnT
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

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
