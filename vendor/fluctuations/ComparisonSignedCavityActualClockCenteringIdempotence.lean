module

public import ComparisonSignedCavityActualOriginalClockGCarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 16000000

theorem nativeOriginalClockResourceResponse_double_freeze
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (U k : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (W : ℝ) :
    nativeOriginalClockResourceResponse P.freeze.freeze U k K b C v₀ q₀ x₀ v q x W=
      -nativeOriginalClockResourceResponse P.freeze U k K b C v₀ q₀ x₀ v q x W := by
  rw [nativeOriginalClockResourceResponse_freeze P.freeze ho,
    nativeOriginalClockResourceResponse_freeze P ho]
  have HV:=funext (fun σ=>P.freeze_value (fullWeight_pos n) (fullFeature n) ho v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ)
  have Hconst (c : ℝ) : T.disorderExpect (fullWeight n) (fullFeature n) v₀ q₀ (fun _=>c) x₀=c := by
    simpa only [mul_one,T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho] using
      T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho v₀ q₀ (fun _=>1) c x₀
  rw [HV,Hconst]
  change -(W⁻¹)^k*(-_)*nativeOriginalLongitudinalPairing n v q x U K b C T
    (fun _=>1) P.live.test.target = _
  ring

theorem nativeOriginalClockStateResponse_double_freeze
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (ho : MassOrdered 0 as)
    (U : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W st.freeze.freeze=
      -nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W st.freeze :=
  nativeOriginalClockResourceResponse_double_freeze st.term ho U st.generation K b C v₀ q₀ x₀ v q x W

theorem nativeOriginalClock_centered_list_frozen_sum
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (ho : MassOrdered 0 as)
    (U : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    (((xs.flatMap (fun Q=>[Q,Q.freeze])).map
      (fun Q=>nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W Q.freeze))).sum=0 := by
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,nativeOriginalClockStateResponse_double_freeze ho,
    add_neg_cancel,List.map_const',List.sum_replicate,nsmul_zero]

theorem nativeOriginalClock_centered_frontier_frozen_sum
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ)
    (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    ((nativeActualWeightedFrontier Γ hs hl nativeActualOriginalGCenteredBranches weight (depth+1) st).map
      (fun Q=>nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W Q.freeze)).sum=0 := by
  rw [nativeActualWeightedFrontier]
  simp only [List.map_flatMap,native_sum_flatMap]
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp ha
  rw [nativeActualOriginalGCenteredBranches,nativeActualWeightedBranchStep_append_center]
  exact nativeOriginalClock_centered_list_frozen_sum ho U K b C v₀ q₀ x₀ v q x W _

end OAI.SKFluctuations.Cavity
