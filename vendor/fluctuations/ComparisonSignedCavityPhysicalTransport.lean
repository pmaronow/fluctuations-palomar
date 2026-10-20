module

public import ComparisonSignedCavityRawReduction
public import CavityNativePhysicalProjectionBridge

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_incoming_projection_fourth_eq_physical (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)) :
    nativeIncomingProjectionFourth n q x center p=
      ((n:ℝ)/(n+1 : ℕ))^4*
        p.tree.cavityLeft.expect (uniformWeight n) (finiteFeature n)
          (fun j => restFiniteVariance n (q j)) (fun σ =>
            (physicalProjectedBoundaryOverlap n
              (clockSteps as (fun j => restFiniteVariance n (q j))) (p.restSpin σ) (restFiniteState n x)-
             physicalProjectedBoundaryOverlap n
              (clockSteps as (fun j => restFiniteVariance n (q j))) (nativeAttachmentOld p σ)
                (restFiniteState n x))^4) (restFiniteState n x) := by
  unfold nativeIncomingProjectionFourth nativeIncomingProjectionDifference
  simp_rw [native_centered_projected_difference_eq_physical n hn as ho q x center]
  rw [restFinite_clockTree_expect n hn]
  unfold ClockTree.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem native_incoming_anchor_fourth_eq_physical (n : ℕ) (hn : 0<n)
    {as : List PositiveMass} (E : ClockTree (Spin n) as)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)) :
    nativeIncomingAnchorFourth n E H s q x p=
      ((n:ℝ)/(n+1 : ℕ))^4*
        p.tree.cavityLeft.expect (uniformWeight n) (finiteFeature n)
          (fun j => restFiniteVariance n (q j)) (fun σ =>
            (inner ℝ
              (WithLp.toLp 2 (normalizedSpin n (nativeAttachmentOld p σ))-
                WithLp.toLp 2 (normalizedSpin n (p.restSpin σ)))
              (physicalWeightedExteriorAnchor n
                (E.realize (fun j => restFiniteVariance n (q j)))
                (fun τ => H ((E.assignmentEquiv (fun j => restFiniteVariance n (q j))).symm τ))
                (E.slotEquiv (fun j => restFiniteVariance n (q j)) s) (restFiniteState n x)))^4)
          (restFiniteState n x) := by
  unfold nativeIncomingAnchorFourth nativeIncomingAnchorDifference
  rw [native_weighted_exterior_anchor_eq_physical n hn]
  simp only [inner_smul_right]
  rw [restFinite_clockTree_expect n hn]
  unfold ClockTree.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end OAI.SKFluctuations.Cavity
