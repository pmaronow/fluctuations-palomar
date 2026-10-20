module

public import ComparisonSignedCavityActualRestRawMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_sampled_rest_physical_raw_eq (n l : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (j : ℕ) (hj : j ≤ as.length) :
    physicalOverlapMoment n l (nativeSampledPhysicalSteps n b h as)
      (Measure.pi (fun i => gaussianReal 0
        (restFiniteVariance n (nativeSampledRestClock n b h 0) i))) id measurable_id j =
      (ClockTree.pairClock as j).disorderExpect (restWeight n) (restFeature n) 0
        (fun k => Sum.elim (fun _ => (b (partitionPoint 0 as k):ℝ))
          (fun _ => (h (partitionPoint 0 as k):ℝ)))
        (fun σ => |orderedOverlap n (ClockTree.pairSpin as j σ).1
          (ClockTree.pairSpin as j σ).2|^(2*l)) 0 := by
  let q : ℕ → RestCoordinate n → ℝ := fun k => Sum.elim
    (fun _ => (b (partitionPoint 0 as k):ℝ))
    (fun _ => (h (partitionPoint 0 as k):ℝ))
  have hs : nativeSampledPhysicalSteps n b h as =
      diagonalBoundarySteps as (restFiniteRealVariance n (q 0))
        (fun k => restFiniteRealVariance n (q (k+1))) := by
    rw [←native_sampled_physical_clock_eq n b h hb hh as ho]
    change clockSteps as (fun k => restFiniteVariance n
      (cumulativeIncrements (q 0) (fun k => q (k+1)) k)) = _
    rw [restFinite_cumulativeIncrements,clockSteps_cumulative]
  have hq0 : (fun i => Real.toNNReal (restFiniteRealVariance n (q 0) i)) =
      restFiniteVariance n (nativeSampledRestClock n b h 0) := by
    rw [←restFiniteVariance_toNNReal]
    congr 1
    funext i
    cases i <;> simp [q,partitionPoint,nativeSampledRestClock]
  have hv : restFiniteRealVariance n 0 = 0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> simp [restFiniteRealVariance]
  have hx : restFiniteState n 0 = 0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> simp [restFiniteState]
  rw [hs,←hq0,physicalOverlapMoment_eq_actual_pair n l as ho
    (fun k => restFiniteRealVariance n (q k)) j hj]
  rw [restFinite_clockTree_disorderExpect n hn,hv,hx]

end OAI.SKFluctuations.Cavity
