module

public import ComparisonActualHighOnlySelectedBadChildFromSharpFailure
public import ComparisonActualHighOnlyAllProfilePullbackHistory
public import ComparisonActualHighOnlyFixedWallHistoryChildMass
public import ComparisonActualHighOnlyMacroChildBudgetFactory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum

theorem ActualFixedWallHighOnlyHistory.eventually_select_bad_child_of_sharp_failure
    {m cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ→ℕ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl≤cu)
    (hAz : 2≤Az) (hCt : 1≤Ct) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0≤1) (hc0D : c0≤D) (hTB : T≤Bclock)
    (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock}
    (G : ActualFixedWallHighOnlyHistory M T c0)
    (hxsunit : ∀n,(M n).xs≤1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam≤(M n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (hroomChild : ∀ᶠn in atTop,
      (M n).lam+(c0*(M n).xs)^2≤(M n).b (M n).data.s)
    (hcross : ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (M n).data.s,
      (M n).b u+(M n).lam+(c0*(M n).xs)^2≤
        (M n).b (M n).data.s)
    (hcost : ∀ᶠn in atTop,
      ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
          (M n).macroChildSweepCost hc0) :
    ∀ᶠn in atTop,
      ∃Q : ActualHighOnlyOverlapMinimum (dim n+1)
        m (m/10000) cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*(M n).xs ∧
        Q.context.E=actualChildErrorBudget (dim n+1)
          (m/10000) c0 (M n).context.d (M n).lam (M n).xs ∧
        (M n).context.N^((m/10000)/4)*(M n).context.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N (m/10000)
          Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs < cl*Q.xs ∨
          cu*Q.xs < Q.alpha.val.val Q.xs) ∧
        Q.data.s=(M n).data.s ∧
        Q.b=(fun u=>(M n).b u-(M n).coefficient u) ∧
        Q.h=(fun u=>(M n).h u+(M n).coefficient u*(M n).R u) := by
  have hdelta : 0 < m/10000 := by positivity
  have hroom : m/10000 < 3*m := by linarith
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith
  have Hselector := hdim.eventually
    (eventually_exists_selected_bad_child_of_sharp_failure
      (D:=D) (Bclock:=Bclock) hm hdelta
      hroom hcl hcu hclcu hAz hCt hC0 hc0 hmargin)
  have Hmass := G.eventually_mass_below_child_cutoff
    hm hmsmall (by linarith : 0≤Az) hC0 hc0 hdim htarget hweak
  have Hclock := G.history.child_pullback_all_profiles G.root_all_profile_pullback
  have Htotal := G.total_root
  have Hs4 : ∀ᶠn in atTop,(G.root n).data.s≤1/4 := by
    have Hs := (G.wall_limits hmsmall hdim).1.eventually
      (eventually_le_nhds (show (0:ℝ)<1/4 by norm_num))
    filter_upwards [G.same_mass, Hs] with n hn hs
    rw [hn]
    exact hs
  have Hweak := hweak.eventually (gt_mem_nhds zero_lt_one)
  filter_upwards [Hselector,Hmass,Hclock,Htotal,G.history.same_omission,
    Hs4,hroomChild,hcross,hcost,htarget,Hweak]
    with n hnSelect hnMass hnClock hnTotal hnSame hnS4 hnRoom hnCross
      hnCost hnTarget hnWeak
  let child := (M n).data.childData (M n).alpha
    (Echild:=actualChildErrorBudget (dim n+1) (m/10000) c0
      (M n).data.d (M n).lam (M n).xs)
    (dchild:=c0*(M n).xs) (M n).lam_mem
    (actual_child_budget_pos (M n).data.hN hc0 (M n).hlam (M n).hxs)
    (mul_pos hc0 (M n).hxs) hnRoom hnCross
  have hchild1 : c0*(M n).xs≤1 := by
    have H := mul_le_mul_of_nonneg_right hc01 (M n).hxs.le
    simp only [one_mul] at H
    exact H.trans (hxsunit n)
  have hchildD : c0*(M n).xs≤D := by
    have H := mul_le_mul_of_nonneg_left (hxsunit n) hc0.le
    simp only [mul_one] at H
    exact H.trans hc0D
  have hmass : (M n).data.s≤comparisonLowerScale child.N child.E child.d := by
    change (M n).data.s≤actualChildCutoff (dim n+1) (m/10000) c0
      (M n).context.d (M n).lam (M n).xs
    exact hnMass
  have hs4M : (M n).data.s≤1/4 := by rw [hnSame];exact hnS4
  have hweakPoint : laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs≤(M n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (M n).hxs)).mp hnWeak.le
  have htotal : ∀u∈Icc (0:ℝ) 1,child.h u+child.b u≤Bclock := by
    intro u hu
    have hr := (omittedSweepQuantile_bounds zero_le_one
      ⟨(M n).data.hs.1,(M n).data.hs1⟩
      (M n).data.hc (M n).data.hk (M n).data.hkc
      (M n).data.hm (M n).data.hM (M n).alpha u).2
    have hc := (M n).coefficient_nonneg u
    have hcR := mul_le_mul_of_nonneg_left hr hc
    change (M n).h u+(M n).coefficient u*(M n).R u+
      ((M n).b u-(M n).coefficient u)≤Bclock
    linarith only [hnTotal.1 u hu,hcR,hTB]
  have hclock : ∀alpha : child.Profile,
      NativePullbackClockRegularity alpha.val.val child.b child.h 0 1 := by
    exact hnClock child rfl rfl rfl
  have hfail : child.N^(20*(m/10000))*child.E < child.cost (child.d^2) := by
    change ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
      (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
        (M n).macroChildSweepCost hc0
    exact hnCost
  exact hnSelect (M n) hnRoom hnCross hchild1 hchildD hs4M
    hmass hnTarget hweakPoint htotal hclock hfail

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
