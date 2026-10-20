module

public import ComparisonSignedCavityActualFourGLinearResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

def nativeOriginalClockFourGStepResponse
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  ((nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    nativeActualOriginalFourGBranches
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) st).map
    (nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W)).sum

theorem nativeResourceFrozenValue_double_freeze
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) :
    P.freeze.freeze.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀=
    fun σ=> -P.freeze.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ := by
  have HV:=funext (fun σ=>P.freeze_value (fullWeight_pos n) (fullFeature n) ho v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ)
  have Hconst (c : ℝ) : T.disorderExpect (fullWeight n) (fullFeature n) v₀ q₀ (fun _=>c) x₀=c := by
    simpa only [mul_one,T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho] using
      T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho v₀ q₀ (fun _=>1) c x₀
  funext σ
  rw [P.freeze.freeze_value (fullWeight_pos n) (fullFeature n) ho,HV,Hconst]

theorem nativeOriginalClockFourGStepResponse_double_freeze
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeOriginalClockFourGStepResponse hs hU K b C v₀ q₀ x₀ v q x W st.freeze.freeze=
      -nativeOriginalClockFourGStepResponse hs hU K b C v₀ q₀ x₀ v q x W st.freeze := by
  unfold nativeOriginalClockFourGStepResponse
  rw [nativeOriginalClockFourGBranches_eq_functional ho hs hU st.freeze.freeze K b C
      v₀ q₀ x₀ v q x W hW,
    nativeOriginalClockFourGBranches_eq_functional ho hs hU st.freeze K b C
      v₀ q₀ x₀ v q x W hW]
  change (W⁻¹)^st.generation/_*nativeOriginalFourResourceFunctional n v q x U K b C st.tree
      (st.term.freeze.freeze.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀) st.term.live.test.target star=
    -((W⁻¹)^st.generation/_*nativeOriginalFourResourceFunctional n v q x U K b C st.tree
      (st.term.freeze.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀) st.term.live.test.target star)
  rw [nativeResourceFrozenValue_double_freeze st.term ho]
  have Hneg:=nativeOriginalFourResourceFunctional_const_mul n v q x U K b C st.tree ho
    (st.term.freeze.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀)
    st.term.live.test.target star (-1)
  simp only [neg_one_mul] at Hneg
  rw [Hneg]
  ring

theorem nativeOriginalClockFourGStepResponse_centered_list_frozen_sum
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    ((xs.flatMap (fun Q=>[Q,Q.freeze])).map
      (fun Q=>nativeOriginalClockFourGStepResponse hs hU K b C v₀ q₀ x₀ v q x W Q.freeze)).sum=0 := by
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,nativeOriginalClockFourGStepResponse_double_freeze ho hs hU K b C
      v₀ q₀ x₀ v q x W hW,add_neg_cancel,List.map_const',List.sum_replicate,nsmul_zero]

theorem nativeOriginalClockFourGBranches_centered_response
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (W : ℝ) :
    let Γ:=nativeOriginalHighRowGamma (n:=n) U K
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
    let children:=nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
      nativeActualOriginalFourGBranches weight st
    let F:=nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W
    ((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
      nativeActualOriginalFourGCenteredBranches weight st).map F).sum=
      (children.map F).sum+(children.map (fun Q=>F Q.freeze)).sum := by
  dsimp only
  rw [nativeActualOriginalFourGCenteredBranches,nativeActualWeightedBranchStep_append_center]
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero]
  exact List.sum_map_add

end OAI.SKFluctuations.Cavity
