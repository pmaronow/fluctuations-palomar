module

public import CavityEndpointLaw
public import CavityCompletedScalar
public import CavityRowMomentTransfer
public import CavityPhysicalForkLawBridge

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem cavityPath_deleted_moment_le_physicalStar (n l U : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    {a t : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    {b h K : ℕ → ℝ} (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j)
    (s r : T.Slot) (hsr : s ≠ r) (hj : T.splitIndex s r ≤ as.length) (S : ℝ) :
    let j := T.splitIndex s r
    let R := ClockTree.pairClock (S:=Spin (n+1)) as j
    let q := physicalCompletedClock (n+1) b h
    let steps := diagonalBoundarySteps as (q 0) (fun k => q (k+1))
    let μ := Measure.pi (fun i => gaussianReal 0 (Real.toNNReal (q 0 i)))
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U a t (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (fun σ => |deletedOverlap n (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ r))-S|^(2*l)) 0 ≤
      Real.exp (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*
        (K as.length+b as.length+h as.length))*(2:ℝ)^(2*l-1)*
        (Real.exp (2*(7*(R.leaves:ℝ)+8*(R.leaves:ℝ)^2*(R.leaves+1:ℝ))*
          (b as.length/2))*physicalStarPairMoment (n+1) l steps μ id measurable_id j S+
          (1/(n+1:ℕ):ℝ)^(2*l)) := by
  dsimp only
  have hq : ∀ i : RestCoordinate n,
      Monotone (fun j => Sum.elim (fun _ => b j) (fun _ => h j) i) := by
    intro i; rcases i with i|i <;> first | exact hb | exact hh
  have hq0 : ∀ j (i : RestCoordinate n),
      0 ≤ Sum.elim (fun _ => b j) (fun _ => h j) i := by
    intro j i; rcases i with i|i <;> first | exact hb0 j | exact hh0 j
  have H := cavityPath_deleted_moment_le_endpoint n (2*l) U T ho ha ht
    hq hb hh hK hq0 hb0 hh0 hK0 s r S 0
  rw [fullEndpoint_overlap_moment_eq_nullCompletedPair n (2*l) U b h K T ho s r hsr S] at H
  let R := ClockTree.pairClock (S:=Spin (n+1)) as (T.splitIndex s r)
  let P := fun σ : R.Assignment => |orderedOverlap (n+1)
    (ClockTree.pairSpin as (T.splitIndex s r) σ).1
    (ClockTree.pairSpin as (T.splitIndex s r) σ).2-S|^(2*l)
  have HC := completed_scalar_expect_close (n+1) R ho hb hh hb0 hh0 P
    (fun σ => pow_nonneg (abs_nonneg _) _)
  have HS := physicalStarPairMoment_eq_pairDisorder (n+1) l as ho
    (physicalCompletedClock (n+1) b h) (T.splitIndex s r) hj S
  change physicalStarPairMoment _ _ _ _ _ _ _ _ = R.disorderExpect _ _ _ _ P 0 at HS
  rw [← HS] at HC
  exact H.trans (mul_le_mul_of_nonneg_left (add_le_add HC.le_mul le_rfl)
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num) _)))

end OAI.SKFluctuations.Cavity
