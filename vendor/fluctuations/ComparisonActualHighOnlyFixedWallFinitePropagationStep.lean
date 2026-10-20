module

public import ComparisonActualHighOnlyFixedWallBadChildCostDichotomy
public import ComparisonActualHighOnlyFixedWallBadChildSelection
public import ComparisonActualHighOnlyFiniteBadChildHistoryStep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 26000000
namespace ActualHighOnlyOverlapMinimum

theorem exists_fixed_wall_weak_bad_parent_finite_child_step_constants
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 margin : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → cl≤cu →
        2≤Az → 1≤Ct → 0 < C0 →
        ∀ hc0 : 0 < c0, c0≤1 → c0≤D → (beta:ℝ)^2≤Bclock →
        cl≤lower → upper≤cu →
        cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ→ℕ, Tendsto dim atTop atTop →
        ∀ M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        ∀ G : ActualFixedWallHighOnlyHistory M ((beta:ℝ)^2) c0,
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
    exists_fixed_wall_bad_parent_sharp_child_cost_failure_constants hbeta hTemp
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
  have Hselected := G.eventually_select_bad_child_of_sharp_failure
    hm hmsmall hcl hcu hclcu hAz hCt hC0 hc0 hc01 hc0D hTB hdim
    hunit htarget hweak HroomChild Hcross Hfail
  exact selected_bad_child_extends_finite_histories Hfinite Herror
    hunit htarget hweak Hselected

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
