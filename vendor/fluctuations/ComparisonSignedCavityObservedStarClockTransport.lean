module

public import ComparisonSignedCavitySubtreeProjectionRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_sampled_physical_clock_eq (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
      (fun _=>(b (partitionPoint 0 as j):ℝ)) (fun _=>(h (partitionPoint 0 as j):ℝ))
    clockSteps as (fun j=>restFiniteVariance n (cumulativeIncrements (q 0) (fun k=>q (k+1)) j))=
      nativeSampledPhysicalSteps n b h as := by
  dsimp only
  let Q:=fun u=>restFiniteVariance n (nativeSampledRestClock n b h u)
  have hQ : ∀i,MonotoneOn (fun u=>Q u i) (Icc (0:ℝ) 1) := by
    intro i u hu v hv huv
    cases i with
    | inl i => exact hh hu hv huv
    | inr i => cases i with
      | none => exact le_rfl
      | some i => exact mul_le_mul_of_nonneg_left (hb hu hv huv) (show (0:ℝ≥0) ≤ restFiniteEdgeScale n from zero_le)
  have hvalues : stepClockValues (fun i=>(Q 0 i:ℝ)) (sampleClockSteps Q 0 as)=
      fun j=>restFiniteRealVariance n (Sum.elim
        (fun _=>(b (partitionPoint 0 as j):ℝ)) (fun _=>(h (partitionPoint 0 as j):ℝ))) := by
    funext j i
    rw [sampleClockSteps_values Q hQ as ho,partitionValues_point]
    cases i with
    | inl i => rfl
    | inr i => cases i with
      | none => rfl
      | some i => simp [Q,nativeSampledRestClock,restFiniteVariance,restFiniteRealVariance]
  rw [restFinite_cumulativeIncrements]
  have H:=sampled_clockSteps_native n Q as ho
  dsimp only at H
  rw [hvalues] at H
  exact H

theorem native_star_suffix_clock_eq_drop (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as pre mid tail : List PositiveMass) (ho : MassOrdered 0 as)
    (hcut : pre++(mid++tail)=as) :
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
      (fun _=>(b (partitionPoint 0 as j):ℝ)) (fun _=>(h (partitionPoint 0 as j):ℝ))
    clockSteps tail (fun j=>restFiniteVariance n (nativeStarSuffixClock n pre mid q j))=
      (nativeSampledPhysicalSteps n b h as).drop (pre.length+mid.length) := by
  dsimp only
  rw [←native_sampled_physical_clock_eq n b h hb hh as ho]
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(b (partitionPoint 0 as j):ℝ)) (fun _=>(h (partitionPoint 0 as j):ℝ))
  let inc:=fun j=>restFiniteVariance n (cumulativeIncrements (q 0) (fun k=>q (k+1)) j)
  change clockSteps tail (fun j=>inc (pre.length+(mid.length+j)))=
    (clockSteps as inc).drop (pre.length+mid.length)
  conv_rhs => rw [←hcut,clockSteps_append,clockSteps_append]
  simp only [List.drop_append,length_clockSteps,Nat.add_sub_cancel_left,Nat.sub_self,List.drop_zero]
  rw [List.drop_eq_nil_of_le (by simp only [length_clockSteps];omega)]
  rw [List.drop_eq_nil_of_le (by simp only [length_clockSteps];exact le_rfl)]
  simp only [List.nil_append]

end OAI.SKFluctuations.Cavity
