module

public import CavityPairSlots

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem cavityPath_pairDeleted_moment_le_physicalStar (n l U : ℕ)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    {a t : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    {b h K : ℕ → ℝ} (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j)
    (j : ℕ) (hj : j ≤ as.length) (S : ℝ) :
    let q := physicalCompletedClock (n+1) b h
    let steps := diagonalBoundarySteps as (q 0) (fun k => q (k+1))
    let μ := Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))
    (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U a t (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (fun σ => |deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-S|^(2*l)) 0 ≤
      Real.exp (220*(K as.length+b as.length+h as.length))*(2:ℝ)^(2*l-1)*
        (Real.exp (110*b as.length)*physicalStarPairMoment (n+1) l steps μ id measurable_id j S+
          (1/(n+1:ℕ):ℝ)^(2*l)) := by
  dsimp only
  let T := ClockTree.pairClock (S:=Spin n × Bool) as j
  let s := ClockTree.pairLeftSlot (S:=Spin n × Bool) as j
  let r := ClockTree.pairRightSlot (S:=Spin n × Bool) as j
  have hsplit : T.splitIndex s r = j := by
    simpa only [T,s,r,Nat.min_eq_left hj] using ClockTree.pairSlots_splitIndex (S:=Spin n × Bool) as j
  have H := cavityPath_deleted_moment_le_physicalStar n l U T ho ha ht hb hh hK hb0 hh0 hK0
    s r (ClockTree.pairSlots_distinct as j) (hsplit ▸ hj) S
  dsimp only at H
  simp only [T,s,r,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot,hsplit,
    ClockTree.pairSlots_splitIndex,Nat.min_eq_left hj,ClockTree.pairClock_leaves] at H
  convert H using 1 <;> ring

end OAI.SKFluctuations.Cavity
