module

public import ComparisonSignedCavityOriginalHighMeanRestoration
public import ComparisonSignedCavityCompletedScalarExact
public import ComparisonNativeCavityGoodStarTransfer

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem fullEndpoint_overlap_mean_eq_physical (n U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (hst : s ≠ t) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (fun σ => orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))) 0 = finitePhysicalMean (n+1) as b h (T.splitIndex s t) := by
  let e := spinEquiv n
  let R := T.relabelSpin e
  let s' := T.relabelSlot e s
  let t' := T.relabelSlot e t
  have hst' : s' ≠ t' := fun H => hst ((T.relabelSlot e).injective H)
  have H := fullEndpointExpect_eq_nullCompleted n U b h K T
    (fun σ => orderedOverlap (n+1) (R.atSlot σ s') (R.atSlot σ t'))
  dsimp only [R,s',t',e] at H
  simp only [ClockTree.atSlot_relabel] at H
  change T.disorderExpect _ _ _ _ _ _ = R.disorderExpect _ _ _ _
    (fun σ => orderedOverlap (n+1) (R.atSlot σ s') (R.atSlot σ t')) 0 at H
  rw [completed_scalar_expect_eq (n+1) R ho b h] at H
  rw [R.disorderExpect_pairAtSlot_actual (uniformWeight_pos (n+1)) (finiteFeature (n+1)) ho
    0 (physicalCompletedClock (n+1) b h) 0 s' t' hst' (orderedOverlap (n+1))] at H
  dsimp only [R,s',t',e] at H
  rw [ClockTree.splitIndex_relabel] at H
  exact H.trans (finitePhysicalMean_eq_actual_pair (n+1) ho b h _
    (T.splitIndex_le_clockLength s t)).symm

theorem fullEndpoint_deleted_centered_mean_abs_le (n U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (hst : s ≠ t) (center : ℝ) :
    |T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (fun σ => deletedOverlap n (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))-center) 0| ≤
      1/(n+1:ℕ)+|finitePhysicalMean (n+1) as b h (T.splitIndex s t)-center| := by
  have H := original_deleted_centered_mean_abs_le n T ho
    (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K) s t hst center
  have HE := T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0
    (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K) 0 s t hst
    (fun σ τ => orderedOverlap (n+1) (joinSpin σ) (joinSpin τ))
  rw [←HE,fullEndpoint_overlap_mean_eq_physical n U b h K T ho s t hst] at H
  exact H

theorem fullEndpoint_deleted_physical_center_mean_abs_le (n U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (hst : s ≠ t) :
    |T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (fun σ => deletedOverlap n (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))-finitePhysicalMean (n+1) as b h (T.splitIndex s t)) 0| ≤
      1/(n+1:ℕ) := by
  simpa only [sub_self,abs_zero,add_zero] using fullEndpoint_deleted_centered_mean_abs_le
    n U b h K T ho s t hst (finitePhysicalMean (n+1) as b h (T.splitIndex s t))

theorem eventually_original_endpoint_center_mean_abs_le
    (n U : ℕ) (bf hf : ℝ → ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1)
    (u : PositiveMass) (hu : u∈us) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠj : ℕ in atTop,
      let as := finiteCutMasses us j
      let b := fun k => (bf (partitionPoint 0 as k):ℝ)
      let h := fun k => (hf (partitionPoint 0 as k):ℝ)
      ∀(T : ClockTree (Spin n×Bool) as) (K : ℕ → ℝ) (s t : T.Slot),s ≠ t →
        T.splitIndex s t=retainedMassPrefixIndex u.val as →
        |T.disorderExpect (fullWeight n) (fullFeature n) 0
          (cavityPath n U 1 1 (fun k => Sum.elim (fun _ => b k) (fun _ => h k)) b h K)
          (fun σ => deletedOverlap n (joinSpin (T.atSlot σ s))
            (joinSpin (T.atSlot σ t))-orderedPathS (n+1) bf hf u.val) 0| ≤
          1/(n+1:ℕ)+eps := by
  have H := LaplaceWindowFormalization.nativeRetainedFinitePhysicalMean_tendsto n bf hf hb hh us hus u hu
  have Habs := (H.sub_const (orderedPathS (n+1) bf hf u.val)).abs
  simp only [sub_self,abs_zero] at Habs
  have HE := Habs.eventually (gt_mem_nhds heps)
  filter_upwards [HE] with j hj
  dsimp only at hj ⊢
  intro T K s t hst hcut
  have HM := fullEndpoint_deleted_centered_mean_abs_le n U
    (fun k => (bf (partitionPoint 0 (finiteCutMasses us j) k):ℝ))
    (fun k => (hf (partitionPoint 0 (finiteCutMasses us j) k):ℝ)) K T
    (finiteCutMasses_ordered us hus j) s t hst (orderedPathS (n+1) bf hf u.val)
  rw [hcut] at HM
  exact HM.trans (add_le_add (le_refl _) hj.le)

end OAI.SKFluctuations.Cavity
