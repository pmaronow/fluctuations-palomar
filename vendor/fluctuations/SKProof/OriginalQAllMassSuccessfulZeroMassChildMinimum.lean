module

public import SKProof.OriginalQAllMassZeroMassOuterRadius
public import ComparisonActualHighWallThetaZeroHighOnlySourceClocks
public import ComparisonActualShiftedAllMassZeroDataBridge
public import ComparisonActualHighWallSuccessfulChildMinimumAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

namespace ActualShiftedAllMassParentChildCall

theorem bare_clocks_eq_original_theta_zero_q_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : ActualShiftedAllMassParentChildCall n delta)
    (Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcontext : a.context =
      Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld)
    (hR : a.R = Q.data.wallRadius Q.alpha) :
    (fun u => a.context.b u-a.coefficient u) = Q.changedBare ∧
    (fun u => a.context.h u+a.coefficient u*a.R u) = Q.changedField := by
  have Hcoef : a.context.coefficient a.alpha =
      omittedStrengthCoefficient Q.data.d Q.data.s
        (Q.data.wallRadius Q.alpha) Q.lam := by
    change omittedStrengthCoefficient a.context.d a.context.s a.R
      a.context.lam = _
    rw [hR,hcontext]
    rfl
  constructor
  · change (fun u => a.context.b u-a.context.coefficient a.alpha u) =
      Q.changedBare
    rw [Hcoef,hcontext]
    rfl
  · change (fun u => a.context.h u+a.context.coefficient a.alpha u*a.R u) =
      Q.changedField
    rw [Hcoef,hR,hcontext]
    rfl

end ActualShiftedAllMassParentChildCall

namespace ActualThetaZeroOverlapMinimum

theorem eventually_exists_theta_zero_successful_all_mass_child_minimum_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl)
    (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (Q : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (a : (n : ℕ) → ActualShiftedAllMassParentChildCall (dim n+1) delta)
    (hxs0 : Tendsto (fun n => (Q n).xs) atTop (𝓝 0))
    (hcontext : ∀n, (a n).context =
      (Q n).data.thetaZeroShiftedParentData
        (Q n).lam (Q n).hlam (Q n).hld)
    (hR : ∀n, (a n).R = (Q n).data.wallRadius (Q n).alpha)
    (hchild : ∀ᶠn in atTop,
      (a n).childRadius = c0*(Q n).xs ∧
      (a n).childLam = (c0*(Q n).xs)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (Q n).data.d (Q n).lam (Q n).xs)
    (hEchild : ∀ᶠn in atTop, (a n).childData.E =
      actualChildErrorBudget (dim n+1) delta c0
        (Q n).data.d (Q n).lam (Q n).xs)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (Q n).data.N delta
        (Q n).data.E (Q n).lam ≤ (Q n).xs)
    (hT : ∀ᶠn in atTop, (Q n).data.T ≤ T)
    (hweak : Tendsto (fun n => laplaceComparisonStrength
      (Q n).data.d (Q n).lam (Q n).xs/(Q n).xs^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n => (Q n).data.s/(Q n).xs)
      atTop (𝓝 0))
    (hr : Tendsto (fun n => (Q n).data.rmin/(Q n).xs)
      atTop (𝓝 0)) :
    ∃C : ℝ, 1 ≤ C ∧ Az ≤ 4*C/cl ∧ ∀ᶠn in atTop,
      ∃V : ActualHighOnlyOverlapMinimum (dim n+1) m delta
        (cl/4) (4*cu) (4*C/cl) C0 1 1 T,
        V.data.E = (a n).childData.E ∧
        V.data.d = (a n).childRadius ∧
        V.data.s = 0 ∧
        V.data.b = (Q n).changedBare ∧
        V.data.h = (Q n).changedField ∧
        V.lam = (a n).childLam ∧
        HEq V.alpha (a n).childAlpha ∧
        V.xs = (Q n).xs ∧
        V.z = min ((4*C/cl)*(Q n).xs) 1 ∧
        V.R = (a n).Z := by
  have hx n : 0 < (Q n).xs := (Q n).hxs
  obtain ⟨Cold,hCold,HquantOld⟩ :=
    theta_zero_successful_all_mass_child_outer_radius_bounds_original_q
      hm hdelta hcl hcu hAz hC0 hc0 dim hdim Q a hxs0
      hcontext hR hchild hweak hs hr
  let C := max Cold (cl*Az/4)
  have hC : 1 ≤ C := hCold.trans (le_max_left _ _)
  have hAzChild : Az ≤ 4*C/cl := by
    apply (le_div_iff₀ hcl).mpr
    have H : cl*Az/4 ≤ C := le_max_right _ _
    nlinarith only [H]
  have Hquant : ∀ᶠn in atTop, ∀u∈Icc (C*(Q n).xs) 1,
      u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl := by
    filter_upwards [HquantOld] with n hn
    intro u hu
    exact hn u ⟨(mul_le_mul_of_nonneg_right
      (le_max_left _ _) (hx n).le).trans hu.1,hu.2⟩
  have hcl1 : cl ≤ 1 := by
    have H := ((Q 0).regular 1 ⟨(Q 0).hz.2,le_rfl⟩).1
    simpa only [mul_one,(Q 0).alpha.property.2.1] using H
  have hcu1 : 1 ≤ cu := by
    have H := ((Q 0).regular 1 ⟨(Q 0).hz.2,le_rfl⟩).2
    simpa only [mul_one,(Q 0).alpha.property.2.1] using H
  have Hdim : Tendsto (fun n => dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have Hgrow := Hdim.eventually
    (eventually_actual_child_parameters_from_target hm hdelta
      (show 0 < 1/C0 by positivity) hc0 hmargin)
  have Hweak := hweak.eventually (gt_mem_nhds zero_lt_one)
  have Hunit := hxs0.eventually
    (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨C,hC,hAzChild,?_⟩
  filter_upwards [Hquant,hchild,hEchild,htarget,hT,Hgrow,Hweak,Hunit]
    with n hnQuant hnChild hnE hnTarget hnT hnGrow hnWeak hnUnit
  have hupper : Real.sqrt ((dim n+1:ℕ):ℝ)*(a n).childData.E ≤
      (a n).childRadius^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr (Q n).data.hN)).mp
      (actual_child_budget_ceiling (dim n+1) delta c0
        (Q n).data.d (Q n).lam (Q n).xs)
    rw [hnE]
    change _ ≤ (a n).childRadius^2
    rw [hnChild.1]
    simpa only [actualChildRadius,mul_comm] using H
  have hparentlower : (1/C0)*((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*
      (Q n).data.d ≤ (Q n).data.E := by
    have H := mul_le_mul_of_nonneg_left
      (Q n).hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hparentupper : (Q n).data.E ≤
      (Q n).data.d^2/Real.sqrt ((dim n+1:ℕ):ℝ) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (Q n).data.hN)).mpr
    simpa only [mul_comm] using (Q n).hupper
  have hparentweak : laplaceComparisonStrength (Q n).data.d
      (Q n).lam (Q n).xs ≤ (Q n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (hx n))).mp hnWeak.le
  have Hg := hnGrow (Q n).data.d (Q n).lam
    (Q n).data.E (Q n).xs (Q n).data.hd
    (Q n).hlam (Q n).hld (Q n).data.hE (hx n)
    hparentlower hparentupper hnTarget hparentweak
  have hlower : ((dim n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*
      (a n).childRadius ≤ C0*(a n).childData.E := by
    have H := mul_le_mul_of_nonneg_left Hg.1 hC0.le
    change _*(a n).childRadius ≤ _
    rw [hnChild.1,hnE]
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul,
      actualChildRadius] using H
  have Hbare := (a n).bare_clocks_eq_original_theta_zero_q_original_q
    (Q n) (hcontext n) (hR n)
  have htotal : ∀u∈Icc (0:ℝ) 1,
      ((a n).context.h u+(a n).coefficient u*(a n).R u)+
      ((a n).context.b u-(a n).coefficient u) ≤ T := by
    intro u hu
    change (fun u => (a n).context.h u+
      (a n).coefficient u*(a n).R u) u+
      (fun u => (a n).context.b u-(a n).coefficient u) u ≤ T
    rw [Hbare.1,Hbare.2]
    exact ((Q n).changed_total_clock_le_temperature hu).trans hnT
  have hdD : (a n).childRadius ≤ (1:ℝ) := by
    rw [hnChild.1]
    exact (mul_le_mul_of_nonneg_right hc01 (hx n).le).trans
      (by simpa using hnUnit)
  have hfull : (a n).childLam = (a n).childRadius^2 := by
    rw [hnChild.1]
    exact hnChild.2.1
  have hroom : (a n).childRadius^2 ≤
      (a n).context.b 0-(a n).coefficient 0 := by
    rw [←hfull]
    exact (a n).matrixRoom
  let data := (a n).zeroMassData (Q n).data.hq hroom
  let A := ((a n).zeroMassMinimum (Q n).data.hq hroom).relam hfull
  have hQuant : ∀u∈Icc (C*(Q n).xs) 1,
      u/(4*cu) ≤ data.R A.alpha u ∧
      data.R A.alpha u ≤ 4*u/cl := by
    intro u hu
    dsimp only [A]
    rw [ActualHighOnlyComparisonMinimum.relam_alpha]
    change u/(4*cu) ≤ (a n).Z u ∧ (a n).Z u ≤ 4*u/cl
    exact hnQuant u hu
  let V := data.successfulChildMinimum hc0 hc01 (hx n)
    hcl hcu hcl1 hcu1 hC A hnChild.1 hdD hupper hlower
    htotal hQuant
  refine ⟨V,rfl,rfl,rfl,?_,?_,?_,?_,rfl,rfl,?_⟩
  · change (fun u => (a n).context.b u-(a n).coefficient u) =
      (Q n).changedBare
    exact Hbare.1
  · change (fun u => (a n).context.h u+
      (a n).coefficient u*(a n).R u) = (Q n).changedField
    exact Hbare.2
  · change (a n).childRadius^2 = (a n).childLam
    exact hfull.symm
  · change HEq A.alpha (a n).childAlpha
    dsimp only [A]
    rw [ActualHighOnlyComparisonMinimum.relam_alpha]
    rfl
  · change data.R A.alpha = (a n).Z
    dsimp only [A]
    rw [ActualHighOnlyComparisonMinimum.relam_alpha]
    rfl

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
