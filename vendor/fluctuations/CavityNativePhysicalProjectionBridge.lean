module

public import CavityRestFiniteTreeLaw
public import CavityNativeProjectedPowerMoments
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockZeroRefinement

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_weighted_exterior_anchor_eq_physical (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (E : ClockTree (Spin n) as)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) :
    nativeWeightedExteriorAnchor n E H s q x=
      ((n:ℝ)/(n+1 : ℕ)) • physicalWeightedExteriorAnchor n
        (E.realize (fun j=>restFiniteVariance n (q j)))
        (fun σ=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (q j))).symm σ))
        (E.slotEquiv (fun j=>restFiniteVariance n (q j)) s) (restFiniteState n x) := by
  unfold nativeWeightedExteriorAnchor physicalWeightedExteriorAnchor
    ReplicaTree.weightedExteriorVector
  congr 1
  simp_rw [restFinite_clockTree_weight n hn]
  exact Fintype.sum_equiv (E.assignmentEquiv (fun j=>restFiniteVariance n (q j))) _ _
    (fun σ=>by rw [Equiv.symm_apply_apply,E.realize_atSlot]; rfl)

theorem native_projected_deleted_overlap_eq_physical (n : ℕ) (hn : 0 < n)
    (as : List PositiveMass) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (σ : Spin n) :
    nativeProjectedDeletedOverlap n as q x σ=
      ((n:ℝ)/(n+1 : ℕ))*physicalProjectedBoundaryOverlap n
        (clockSteps as (fun j=>restFiniteVariance n (q j))) σ (restFiniteState n x) := by
  unfold nativeProjectedDeletedOverlap
  simp_rw [deleted_overlap_join_eq_scaled]
  rw [restFinite_clockTree_expect n hn]
  have he : (ClockTree.single (S := Spin n) as).expect (uniformWeight n) (finiteFeature n)
      (fun j=>restFiniteVariance n (q j))
      (fun τ=>((n:ℝ)/(n+1 : ℕ))*orderedOverlap n σ (ClockTree.singleEquiv (S := Spin n) as τ))
      (restFiniteState n x)=
    ((n:ℝ)/(n+1 : ℕ))*ClockTree.singleMean (uniformWeight n) (finiteFeature n)
      as (fun j=>restFiniteVariance n (q j)) (orderedOverlap n σ) (restFiniteState n x) := by
    unfold ClockTree.singleMean ClockTree.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    ring
  rw [he,ClockTree.singleMean_eq_hierarchy (uniformWeight_pos n) (finiteFeature n) ho,
    ←physical_projected_overlap_eq_fresh_mean n _ (clockSteps_ordered ho _)]

theorem native_centered_projected_difference_eq_physical (n : ℕ) (hn : 0 < n)
    (as : List PositiveMass) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (center : ℝ) (σ τ : Spin n) :
    nativeCenteredProjectedDeletedOverlap n as q x center σ-
      nativeCenteredProjectedDeletedOverlap n as q x center τ=
    ((n:ℝ)/(n+1 : ℕ))*(physicalProjectedBoundaryOverlap n
        (clockSteps as (fun j=>restFiniteVariance n (q j))) σ (restFiniteState n x)-
      physicalProjectedBoundaryOverlap n
        (clockSteps as (fun j=>restFiniteVariance n (q j))) τ (restFiniteState n x)) := by
  unfold nativeCenteredProjectedDeletedOverlap
  rw [native_projected_deleted_overlap_eq_physical n hn as ho,
    native_projected_deleted_overlap_eq_physical n hn as ho]
  ring

end OAI.SKFluctuations.Cavity
