module

public import ComparisonActualHighOnlyFiniteMatrixGapRoom

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualHighOnlyOverlapMinimum

structure ActualFiniteWeakHighOnlyHistory
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ → ℕ}
    (c0 : ℝ)
    (root : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (q : ℕ)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock) : Prop where
  weak : ActualWeakHighOnlyHistoryChain c0 root M
  matrix : ActualFiniteHighOnlyMatrixHistory c0 root q M

namespace ActualFiniteWeakHighOnlyHistory
variable {m delta cl cu Az C0 Ct D Bclock c0 margin : ℝ} {dim : ℕ → ℕ}

theorem root
    (R : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock) :
    ActualFiniteWeakHighOnlyHistory c0 R 0 R :=
  ⟨.root,.root⟩

theorem child
    {q : ℕ}
    {R P Q : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (H : ActualFiniteWeakHighOnlyHistory c0 R q P)
    (x : ℕ → ℝ) (hx : ∀n,0<x n) (hunit : ∀ᶠn in atTop,x n≤1)
    (htarget : ∀ᶠn in atTop,
      comparisonConditionalScale (P n).context.N delta (P n).context.E (P n).lam≤x n)
    (hcap : ∀ᶠn in atTop,(P n).z≤Az*x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d
      (P n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hd : ∀ᶠn in atTop,(Q n).context.d=actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop,(Q n).context.E=actualChildErrorBudget (dim n+1)
      delta c0 (P n).context.d (P n).lam (x n))
    (hs : ∀ᶠn in atTop,(Q n).data.s=(P n).data.s)
    (hb : ∀ᶠn in atTop,∀u,(Q n).b u=(P n).b u-(P n).coefficient u)
    (hh : ∀ᶠn in atTop,∀u,(Q n).h u=(P n).h u+
      (P n).coefficient u*(P n).R u) :
    ActualFiniteWeakHighOnlyHistory c0 R (q+1) Q :=
  ⟨.child H.weak x hx hunit htarget hcap hweak hd hE hs hb hh,
    .child H.matrix x hunit hd hs hb⟩

theorem next_child_room
    (hc0 : 0≤c0)
    {q : ℕ}
    {R M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (H : ActualFiniteWeakHighOnlyHistory c0 R q M)
    (hrootCap : ∀ᶠn in atTop,(R n).context.d≤c0)
    (hrootGap : ∀ᶠn in atTop,∀u∈Ico (0:ℝ) (R n).data.s,
      (R n).b u+margin≤(R n).b (R n).data.s)
    (hrootPos : ∀ᶠn in atTop,0<(R n).data.s)
    (hbudget : ((q:ℝ)+2)*c0^2≤ margin)
    (x : ℕ → ℝ) (hx : ∀n,0<x n) (hunit : ∀ᶠn in atTop,x n≤1) :
    ∀ᶠn in atTop,
      (M n).lam+(c0*x n)^2≤(M n).b (M n).data.s ∧
      ∀u∈Ico (0:ℝ) (M n).data.s,
        (M n).b u+(M n).lam+(c0*x n)^2≤(M n).b (M n).data.s :=
  H.matrix.next_child_room hc0 hrootCap hrootGap hrootPos hbudget x hx hunit

end ActualFiniteWeakHighOnlyHistory
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
