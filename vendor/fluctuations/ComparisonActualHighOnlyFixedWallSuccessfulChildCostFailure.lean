module

public import ComparisonActualHighOnlyFixedWallSuccessfulChildPropagation
public import ComparisonActualHighOnlyMacroChildBudgetFactory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum

theorem eventually_fixed_wall_shrinking_bad_parent_macro_child_cost_failure
    {m cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hclmargin : cl < 2*T*Real.exp (-12*T))
    (hcumargin : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m (m/10000) cl cu Az C0 Ct D Bclock)
    (G : ActualFixedWallHighOnlyHistory M T c0)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (htarget : ∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N
      (m/10000) (M n).context.E (M n).lam ≤ (M n).xs)
    (hweak : Tendsto (fun n => laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (hroomChild : ∀ᶠ n in atTop, (M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s)
    (hcross : ∀ᶠ n in atTop, ∀ u ∈ Ico (0:ℝ) (M n).data.s,
      (M n).b u+(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s)
    (Hbad : ∀ᶠ n in atTop, ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
      (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) :
    ∀ᶠ n in atTop, ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
      (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
        (M n).macroChildSweepCost hc0 := by
  let delta : ℝ := m/10000
  classical
  by_contra Hfailure
  have Hfreq : ∃ᶠn in atTop,
      (M n).macroChildSweepCost hc0 ≤
        ((dim n+1:ℕ):ℝ)^(20*delta)*actualChildErrorBudget (dim n+1)
          delta c0 (M n).context.d (M n).lam (M n).xs := by
    simpa only [Filter.Frequently,not_le,delta] using Hfailure
  obtain ⟨phi,hphi,Hphi⟩ := extraction_of_frequently_atTop
    (Hfreq.and_eventually (hroomChild.and hcross))
  have Hfactory (n : ℕ) :
      ∃a : ActualHighOnlyChildBarrierCall (dim (phi n)+1) delta,
        a.context=(M (phi n)).context ∧
        a.lam=(M (phi n)).lam ∧ a.R=(M (phi n)).R ∧
        a.childRadius=c0*(M (phi n)).xs ∧
        a.childLam=(c0*(M (phi n)).xs)^2 ∧
        a.childData.E=actualChildErrorBudget (dim (phi n)+1) delta c0
          (M (phi n)).context.d (M (phi n)).lam (M (phi n)).xs ∧
        a.childData.s=(M (phi n)).data.s ∧
        a.childData.b=(fun u=>(M (phi n)).b u-(M (phi n)).coefficient u) ∧
        a.childData.h=(fun u=>(M (phi n)).h u+
          (M (phi n)).coefficient u*(M (phi n)).R u) ∧
        a.err=(M (phi n)).macroChildSweepCost hc0 :=
    exists_actual_high_only_macro_child_at_parent_with_budget
      (M (phi n)) hc0 (Hphi n).2.1 (Hphi n).2.2
  choose a haCtx haLam haR haD haChildLam haE haS haB haH haErr
    using Hfactory
  have hparent (n : ℕ) :
      (a n).context.E=(M (phi n)).context.E ∧
      (a n).context.d=(M (phi n)).context.d ∧
      (a n).lam=(M (phi n)).lam ∧
      (a n).R=(M (phi n)).R ∧
      (a n).context.s=(M (phi n)).context.s := by
    refine ⟨?_,?_,haLam n,haR n,?_⟩  <;> rw [haCtx n]
  have hchild : ∀ᶠn in atTop,
      (a n).childRadius=c0*(M (phi n)).xs ∧
      (a n).childLam=(c0*(M (phi n)).xs)^2 ∧
      (a n).err≤((dim (phi n)+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim (phi n)+1) delta c0
          (M (phi n)).context.d (M (phi n)).lam (M (phi n)).xs :=
    Eventually.of_forall (fun n=>⟨haD n,haChildLam n,by
      rw [haErr n]
      exact (Hphi n).1⟩)
  exact eventually_fixed_wall_bad_parent_excludes_successful_child_sequence
    hm hmsmall hcl hcu hAz hC0 hc0 hc01 hclmargin hcumargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp phi hphi) a (fun n=>(M (phi n)).xs)
    (fun _=>le_rfl) (hxlim.comp hphi.tendsto_atTop)
    haCtx haLam haR hchild (Eventually.of_forall haE)
    (hphi.tendsto_atTop.eventually htarget)
    (hweak.comp hphi.tendsto_atTop)
    (hphi.tendsto_atTop.eventually Hbad)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
