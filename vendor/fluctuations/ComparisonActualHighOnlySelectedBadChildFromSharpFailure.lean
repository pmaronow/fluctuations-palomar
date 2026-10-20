module

public import ComparisonActualHighOnlyRegularChildCost
public import ComparisonActualHighOnlySelectedBadScale
public import ComparisonActualHighOnlyChildData
public import ComparisonNativeActualChildParameterGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000

namespace ActualHighOnlyOverlapMinimum

theorem eventually_exists_selected_bad_child_of_sharp_failure
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl ≤ cu) (hAz : 2 ≤ Az)
    (hCt : 1 ≤ Ct) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀hroomM : M.lam+(c0*M.xs)^2≤M.b M.data.s,
      ∀hcross : ∀u∈Ico (0:ℝ) M.data.s,
        M.b u+M.lam+(c0*M.xs)^2≤M.b M.data.s,
      let child := M.data.childData M.alpha
        (Echild:=actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs)
        (dchild:=c0*M.xs) M.lam_mem
        (actual_child_budget_pos M.data.hN hc0 M.hlam M.hxs)
        (mul_pos hc0 M.hxs) hroomM hcross;
      c0*M.xs≤1 → c0*M.xs≤D → M.data.s≤1/4 →
      M.data.s≤comparisonLowerScale child.N child.E child.d →
      comparisonConditionalScale M.data.N delta M.data.E M.lam≤M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs≤M.xs^2 →
      (∀u∈Icc (0:ℝ) 1,child.h u+child.b u≤Bclock) →
      (∀alpha : child.Profile,
        NativePullbackClockRegularity alpha.val.val child.b child.h 0 1) →
      child.N^(20*delta)*child.E<child.cost (child.d^2) →
      ∃Q : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*M.xs ∧
        Q.context.E=actualChildErrorBudget (n+1) delta c0
          M.data.d M.lam M.xs ∧
        M.data.N^(delta/4)*M.data.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N delta
          Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs<cl*Q.xs ∨
          cu*Q.xs<Q.alpha.val.val Q.xs) ∧
        Q.data.s=M.data.s ∧
        Q.b=(fun u=>M.b u-M.coefficient u) ∧
        Q.h=(fun u=>M.h u+M.coefficient u*M.R u) := by
  have hdim : Tendsto (fun n : ℕ=>n+1) atTop atTop :=
    tendsto_add_atTop_nat 1
  filter_upwards [ActualHighOnlyComparisonData.eventually_actual_high_only_regular_child_failure_selects_irregular
      (D:=D) (T:=Bclock) hm hdelta hroom hcl hcu hclcu hC0,
    hdim.eventually (eventually_actual_child_parameters_from_target hm hdelta
      (one_div_pos.mpr hC0) hc0 hmargin)] with n hnFailure hnParams
  intro M hroomM hcross
  dsimp only
  intro hchild1 hchildD hs4 hmass htarget hweak htotal hclock hfail
  let child := M.data.childData M.alpha
    (Echild:=actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs)
    (dchild:=c0*M.xs) M.lam_mem
    (actual_child_budget_pos M.data.hN hc0 M.hlam M.hxs)
    (mul_pos hc0 M.hxs) hroomM hcross
  have hlo : (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d≤M.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hup : M.data.E≤M.data.d^2/Real.sqrt ((n+1:ℕ):ℝ) :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr
      (by simpa only [mul_comm] using M.hupper)
  have hp := hnParams M.data.d M.lam M.data.E M.xs M.data.hd
    M.hlam M.hld M.data.hE M.hxs hlo hup htarget hweak
  have hchildLower : child.N^(-(2:ℝ)/3+m)*child.d≤C0*child.E := by
    have H := mul_le_mul_of_nonneg_left hp.1 hC0.le
    change ((n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*actualChildRadius c0 M.xs≤
      C0*actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs
    simpa only [←mul_assoc,mul_one_div_cancel hC0.ne',one_mul] using H
  have hchildUpper : Real.sqrt child.N*child.E≤child.d^2 := by
    have H := (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mp hp.2.1
    change Real.sqrt M.data.N*actualChildErrorBudget (n+1) delta c0
      M.data.d M.lam M.xs≤(actualChildRadius c0 M.xs)^2
    simpa only [mul_comm] using H
  have hcl1 : cl≤1 := by
    simpa only [M.alpha.property.2.1,mul_one] using
      (M.regular 1 ⟨M.hz.2,le_rfl⟩).1
  have hcu1 : 1≤cu := by
    simpa only [M.alpha.property.2.1,mul_one] using
      (M.regular 1 ⟨M.hz.2,le_rfl⟩).2
  obtain ⟨lam,hlam,alpha,hattained,hbad⟩ := hnFailure child
    hchildD hchild1 hs4 hmass hchildUpper hchildLower htotal hclock hfail
  have hlam0 : 0<lam := (Real.rpow_pos_of_pos child.hN _).trans hlam.1
  obtain ⟨_,_,hminimum⟩ := child.exists_minimum ⟨hlam0.le,hlam.2.le⟩
  let optimizer : ActualHighOnlyComparisonMinimum child lam :=
    ⟨alpha,hattained,fun beta=>hattained.symm ▸ hminimum beta⟩
  obtain ⟨Q,hcontext,hQlam,hAlpha,hxs,hz,hbadQ⟩ :=
    child.exists_selected_bad_scale_minimum_of_attained optimizer
      hlam0 hlam.2.le hdelta.le hchildD hchildUpper hchildLower
      htotal hAz hCt hcl1 hcu1 hbad
  refine ⟨Q,?_,?_,?_,?_,hbadQ,?_,?_,?_⟩
  · change Q.data.d=c0*M.xs
    rw [hcontext]
    rfl
  · change Q.data.E=actualChildErrorBudget (n+1) delta c0 M.data.d M.lam M.xs
    rw [hcontext]
    rfl
  · change M.data.N^(delta/4)*M.data.E≤Q.data.E
    rw [hcontext]
    exact hp.2.2.1
  · change Q.xs∈Icc (comparisonConditionalScale Q.data.N delta Q.data.E Q.lam) 1
    rw [hcontext,hQlam]
    exact hxs
  · rw [hcontext]
    rfl
  · change Q.data.b=(fun u=>M.b u-M.coefficient u)
    rw [hcontext]
    rfl
  · change Q.data.h=(fun u=>M.h u+M.coefficient u*M.R u)
    rw [hcontext]
    rfl

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
