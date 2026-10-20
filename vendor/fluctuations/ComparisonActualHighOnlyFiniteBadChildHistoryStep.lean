module

public import ComparisonActualHighOnlyFiniteWeakHistoryReindex
public import ComparisonActualHighOnlyFiniteErrorHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000

namespace ActualHighOnlyOverlapMinimum

theorem selected_bad_child_extends_finite_histories
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {dim : ℕ→ℕ}
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    {q : ℕ}
    (Hfinite : ActualFiniteWeakHighOnlyHistory c0 root q M)
    (Herror : ActualHighOnlyErrorGrowthHistory root q M)
    (hunit : ∀n,(M n).xs≤1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N
      delta (M n).context.E (M n).lam≤(M n).xs)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0))
    (Hselected : ∀ᶠn in atTop,
      ∃Q : ActualHighOnlyOverlapMinimum (dim n+1)
        m delta cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*(M n).xs ∧
        Q.context.E=actualChildErrorBudget (dim n+1)
          delta c0 (M n).context.d (M n).lam (M n).xs ∧
        (M n).context.N^(delta/4)*(M n).context.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N delta
          Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs<cl*Q.xs ∨
          cu*Q.xs<Q.alpha.val.val Q.xs) ∧
        Q.data.s=(M n).data.s ∧
        Q.b=(fun u=>(M n).b u-(M n).coefficient u) ∧
        Q.h=(fun u=>(M n).h u+(M n).coefficient u*(M n).R u)) :
    ∃N : ℕ,
      ∃Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim (n+N)+1)
        m delta cl cu Az C0 Ct D Bclock,
        ActualFiniteWeakHighOnlyHistory c0
          (fun n=>root (n+N)) (q+1) Q ∧
        ActualHighOnlyErrorGrowthHistory
          (fun n=>root (n+N)) (q+1) Q ∧
        (∀n,(Q n).xs∈Icc (comparisonConditionalScale (Q n).context.N
          delta (Q n).context.E (Q n).lam) 1) ∧
        (∀n,(Q n).alpha.val.val (Q n).xs<cl*(Q n).xs ∨
          cu*(Q n).xs<(Q n).alpha.val.val (Q n).xs) := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp Hselected
  let shift : ℕ→ℕ := fun n=>n+N
  have hshift : StrictMono shift := fun i j hij=>Nat.add_lt_add_right hij N
  have Hready (n:ℕ) :
      ∃Q : ActualHighOnlyOverlapMinimum (dim (shift n)+1)
        m delta cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*(M (shift n)).xs ∧
        Q.context.E=actualChildErrorBudget (dim (shift n)+1)
          delta c0 (M (shift n)).context.d (M (shift n)).lam (M (shift n)).xs ∧
        (M (shift n)).context.N^(delta/4)*(M (shift n)).context.E≤Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N delta
          Q.context.E Q.lam) 1 ∧
        (Q.alpha.val.val Q.xs<cl*Q.xs ∨
          cu*Q.xs<Q.alpha.val.val Q.xs) ∧
        Q.data.s=(M (shift n)).data.s ∧
        Q.b=(fun u=>(M (shift n)).b u-(M (shift n)).coefficient u) ∧
        Q.h=(fun u=>(M (shift n)).h u+
          (M (shift n)).coefficient u*(M (shift n)).R u) :=
    hN (shift n) (by dsimp [shift];omega)
  choose Q hD hE hgrowth hQscale hbad hmass hbare hfield using Hready
  have HF := (Hfinite.comp shift hshift.tendsto_atTop).child
    (fun n=>(M (shift n)).xs)
    (fun n=>(M (shift n)).hxs)
    (Eventually.of_forall (fun n=>hunit (shift n)))
    (hshift.tendsto_atTop.eventually htarget)
    (Eventually.of_forall (fun n=>(M (shift n)).hzxs))
    (hweak.comp hshift.tendsto_atTop)
    (Eventually.of_forall hD) (Eventually.of_forall hE)
    (Eventually.of_forall hmass)
    (Eventually.of_forall (fun n u=>congrFun (hbare n) u))
    (Eventually.of_forall (fun n u=>congrFun (hfield n) u))
  have HE : ActualHighOnlyErrorGrowthHistory
      (fun n=>root (shift n)) (q+1) Q :=
    .child (Herror.comp shift hshift.tendsto_atTop)
      (Eventually.of_forall hgrowth)
  exact ⟨N,Q,HF,HE,hQscale,hbad⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
