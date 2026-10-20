module

public import SKProof.OriginalQHighOnlySuccessfulChild
public import ComparisonActualHighOnlySelectedBadChildFromSharpFailure
public import ComparisonActualHighOnlyAllProfilePullbackHistory
public import ComparisonActualHighOnlyMacroChildBudgetFactory
public import ComparisonActualHighOnlyFiniteBadChildHistoryStep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
namespace ActualHighOnlyOverlapMinimum

theorem OriginalQHighOnlyHistory.eventually_select_bad_child_of_sharp_failure_original_q
    {m cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ→ℕ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hclcu : cl≤cu)
    (hAz : 2≤Az) (hCt : 1≤Ct) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0≤1) (hc0D : c0≤D) (hTB : T≤Bclock)
    (hdim : Tendsto dim atTop atTop)
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock}
    (G : OriginalQHighOnlyHistory M T c0)
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

theorem exists_weak_bad_parent_finite_child_step_constants_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 margin : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → cl≤cu →
        2≤Az → 1≤Ct → 0 < C0 →
        ∀ _hc0 : 0 < c0, c0≤1 → c0≤D → (beta:ℝ)^2≤Bclock →
        cl≤lower → upper≤cu →
        cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ→ℕ, Tendsto dim atTop atTop →
        ∀ M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        ∀ G : OriginalQHighOnlyHistory M ((beta:ℝ)^2) c0,
        ∀ q : ℕ,
        ActualFiniteWeakHighOnlyHistory c0 G.root q M →
        ActualHighOnlyErrorGrowthHistory G.root q M →
        (∀ᶠ n in atTop, (G.root n).context.d≤c0) →
        (∀ᶠ n in atTop, ∀ u∈Ico (0:ℝ) (G.root n).data.s,
          (G.root n).b u+margin≤(G.root n).b (G.root n).data.s) →
        (∀ᶠ n in atTop, 0 < (G.root n).data.s) →
        ((q:ℝ)+2)*c0^2≤ margin →
        (∀ n, (M n).xs≤1) →
        (∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N (m/10000)
          (M n).context.E (M n).lam≤(M n).xs) →
        Tendsto (fun n => laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) →
        (∀ᶠ n in atTop, ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) →
        ∃ N : ℕ,
          ∃ Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim (n+N)+1)
            m (m/10000) cl cu Az C0 Ct D Bclock,
            ActualFiniteWeakHighOnlyHistory c0 (fun n=>G.root (n+N)) (q+1) Q ∧
            ActualHighOnlyErrorGrowthHistory (fun n=>G.root (n+N)) (q+1) Q ∧
            (∀ n, (Q n).xs∈Icc (comparisonConditionalScale (Q n).context.N
              (m/10000) (Q n).context.E (Q n).lam) 1) ∧
            (∀ n, (Q n).alpha.val.val (Q n).xs < cl*(Q n).xs ∨
              cu*(Q n).xs < (Q n).alpha.val.val (Q n).xs) := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hcost⟩ :=
    exists_bad_parent_sharp_child_cost_failure_constants_original_q hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 margin hm hmsmall hcl hcu hclcu
    hAz hCt hC0 hc0 hc01 hc0D hTB hclCost hcuCost hclSlack hcuSlack
    dim hdim M G q Hfinite Herror hrootCap hrootGap hrootPos hbudget
    hunit htarget hweak Hbad
  have Hroom := Hfinite.next_child_room hc0.le hrootCap hrootGap hrootPos
    hbudget (fun n=>(M n).xs) (fun n=>(M n).hxs)
    (Eventually.of_forall hunit)
  have HroomChild : ∀ᶠ n in atTop,
      (M n).lam+(c0*(M n).xs)^2≤(M n).b (M n).data.s :=
    Hroom.mono (fun n hn=>hn.1)
  have Hcross : ∀ᶠ n in atTop, ∀ u∈Ico (0:ℝ) (M n).data.s,
      (M n).b u+(M n).lam+(c0*(M n).xs)^2≤(M n).b (M n).data.s :=
    Hroom.mono (fun n hn=>hn.2)
  have Hfail := Hcost m cl cu Az C0 Ct D Bclock c0
    hm hmsmall hcl hcu (by linarith : 0≤Az) hC0 hc0 hc01
    hclCost hcuCost hclSlack hcuSlack dim hdim M G hunit htarget hweak
    HroomChild Hcross Hbad
  have Hselected := G.eventually_select_bad_child_of_sharp_failure_original_q
    hm hmsmall hcl hcu hclcu hAz hCt hC0 hc0 hc01 hc0D hTB hdim
    hunit htarget hweak HroomChild Hcross Hfail
  exact selected_bad_child_extends_finite_histories Hfinite Herror
    hunit htarget hweak Hselected

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
