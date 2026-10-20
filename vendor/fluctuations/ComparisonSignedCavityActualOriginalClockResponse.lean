module

public import ComparisonSignedCavityActualOriginalGCenteredBranches

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeOriginalClockResourceResponse
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (U k : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) : ℝ :=
  (W⁻¹)^k*nativeOriginalLongitudinalPairing n v q x U K b C T
    (P.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀) P.live.test.target

def nativeOriginalClockStateResponse
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (U : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  nativeOriginalClockResourceResponse st.term U st.generation K b C v₀ q₀ x₀ v q x W

def nativeOriginalClockParentWeight
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (W : ℝ) (U : ℕ) (K : ℕ→ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (beta : ℝ) : ℝ :=
  let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
  W*(beta/(chi*K star))

def nativeOriginalClockGBranchBeta
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (U : ℕ) (K b : ℕ→ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) : ℝ :=
  let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
  (if tag=0 then chi else 1)*b star

theorem nativeOriginalClockResourceResponse_reweight
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (U k : ℕ) (K b C : ℕ→ℝ) (c : ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    nativeOriginalClockResourceResponse (P.reweight c) U k K b C v₀ q₀ x₀ v q x W=
      c*nativeOriginalClockResourceResponse P U k K b C v₀ q₀ x₀ v q x W := by
  unfold nativeOriginalClockResourceResponse
  have HV:=funext (fun σ=>P.reweight_value c (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ)
  rw [HV]
  change (W⁻¹)^k*nativeOriginalLongitudinalPairing n v q x U K b C T
    (fun σ=>c*P.value _ _ _ _ _ _ _ σ) P.live.test.target= _
  rw [native_original_longitudinal_const_mul_test n v q x U K b C T ho]
  ring

theorem nativeOriginalClockResourceResponse_projection
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (U k : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hl : star ≤ as.length) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    nativeOriginalClockResourceResponse (P.projection 0 k hl) U (k+1) K b C v₀ q₀ x₀ v q x W=
      (W⁻¹)^(k+1)*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>F (g.restrict σ)*(R (T.atSlot (g.restrict σ) P.live.test.target) (g.spin σ)-C star))
        (g.embed P.live.test.target) := by
  dsimp only
  unfold nativeOriginalClockResourceResponse
  have HV:=funext (fun σ=>P.projection_value 0 k hl (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ)
  rw [HV]
  rfl

theorem nativeOriginalClockResourceResponse_markedSwitch
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (k : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hs : star < U) (hh : U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark) :
    let g:=nativeFreshAtSlot p.tree 0 (p.embed P.live.test.target) star
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    nativeOriginalClockResourceResponse (P.markedHighSwitch 0 k p hp hs hh) U (k+1)
      K b C v₀ q₀ x₀ v q x W=
      (W⁻¹)^(k+1)*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>F (p.restrict (g.restrict σ))*(R (g.spin σ) (p.spin (g.restrict σ))-C star)) g.mark := by
  dsimp only
  unfold nativeOriginalClockResourceResponse
  have HV:=funext (fun σ=>P.markedHighSwitch_value 0 k p hp hs hh (fullWeight n)
    (fullFeature n) v₀ q₀ (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ)
  rw [HV]
  rfl

theorem nativeOriginalClockWeightedBranchStep_response
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (W : ℝ) :
    ((nativeActualWeightedBranchStep Γ hs hl branches weight st).map
      (nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W)).sum=
    (branches.map (fun branch=>weight st branch.1*
      ((nativeActualResourceExpansion Γ hs hl branch.2 st).map
        (nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W)).sum)).sum := by
  unfold nativeActualWeightedBranchStep
  simp only [List.map_flatMap,native_sum_flatMap,List.map_map,Function.comp_def,
    nativeOriginalClockStateResponse,NativeActualResourceState.reweight]
  simp_rw [nativeOriginalClockResourceResponse_reweight _ ho]
  simp only [List.sum_map_mul_left]
  rfl

theorem nativeOriginalClockResourceResponse_freeze
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (U k : ℕ) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    nativeOriginalClockResourceResponse P.freeze U k K b C v₀ q₀ x₀ v q x W=
      -(W⁻¹)^k*T.disorderExpect (fullWeight n) (fullFeature n) v₀ q₀ F x₀*
        nativeOriginalLongitudinalPairing n v q x U K b C T (fun _=>1) P.live.test.target := by
  dsimp only
  unfold nativeOriginalClockResourceResponse
  have HV:=funext (fun σ=>P.freeze_value (fullWeight_pos n) (fullFeature n) ho v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ)
  rw [HV]
  let mean:=T.disorderExpect (fullWeight n) (fullFeature n) v₀ q₀
    (P.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀) x₀
  have HF : (fun _ : T.Assignment=> -mean)=(fun _=> (-mean)*1) := by funext σ;ring
  change (W⁻¹)^k*nativeOriginalLongitudinalPairing n v q x U K b C T (fun _=> -mean)
    P.live.test.target= -(W⁻¹)^k*mean*_
  rw [HF,native_original_longitudinal_const_mul_test n v q x U K b C T ho]
  ring

end OAI.SKFluctuations.Cavity
