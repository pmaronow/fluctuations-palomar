module

public import ComparisonSignedCavityActualFourGSource
public import ComparisonSignedCavityActualClockCenteringIdempotence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def nativeOriginalResourceChildFunctional (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (F : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C star
  b star*(chi*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
    (fun σ=>F (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
    nativeOriginalFreshPartnerLResponse n v q x U K b C T s star (fun σ c d=>F σ*A c d))

def nativeOriginalFourResourceFunctional (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (F : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star;
  -nativeOriginalResourceChildFunctional n v q x U K b C T F s star+
    (1/2:ℝ)*nativeOriginalResourceChildFunctional n v q x U K b C g.tree
      (fun σ=>F (g.restrict σ)) g.mark star

theorem native_original_longitudinal_add_test (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ) (a : T.Slot) :
    nativeOriginalLongitudinalPairing n v q x U K b C T (fun σ=>P σ+Q σ) a=
      nativeOriginalLongitudinalPairing n v q x U K b C T P a+
      nativeOriginalLongitudinalPairing n v q x U K b C T Q a := by
  simpa only [neg_one_mul,sub_neg_eq_add] using
    native_original_longitudinal_sub_smul n v q x U K b C T P Q a (-1)

theorem native_original_fresh_partner_L_response_add (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (P Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeOriginalFreshPartnerLResponse n v q x U K b C T s star (fun σ c d=>P σ c d+Q σ c d)=
      nativeOriginalFreshPartnerLResponse n v q x U K b C T s star P+
      nativeOriginalFreshPartnerLResponse n v q x U K b C T s star Q := by
  unfold nativeOriginalFreshPartnerLResponse
  dsimp only
  simp_rw [native_original_longitudinal_add_test]
  simp only [mul_add,List.sum_map_add]

theorem nativeOriginalResourceChildFunctional_add (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) :
    nativeOriginalResourceChildFunctional n v q x U K b C T (fun σ=>P σ+Q σ) s star=
      nativeOriginalResourceChildFunctional n v q x U K b C T P s star+
      nativeOriginalResourceChildFunctional n v q x U K b C T Q s star := by
  unfold nativeOriginalResourceChildFunctional
  dsimp only
  simp only [add_mul]
  rw [native_original_longitudinal_add_test,native_original_fresh_partner_L_response_add]
  ring

theorem nativeOriginalResourceChildFunctional_const_mul (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) (c : ℝ) :
    nativeOriginalResourceChildFunctional n v q x U K b C T (fun σ=>c*P σ) s star=
      c*nativeOriginalResourceChildFunctional n v q x U K b C T P s star := by
  unfold nativeOriginalResourceChildFunctional
  dsimp only
  simp only [mul_assoc]
  rw [native_original_longitudinal_const_mul_test n v q x U K b C _ ho,
    native_original_fresh_partner_L_response_const_mul n v q x U K b C _ ho]
  ring

theorem nativeOriginalFourResourceFunctional_add (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P Q : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) :
    nativeOriginalFourResourceFunctional n v q x U K b C T (fun σ=>P σ+Q σ) s star=
      nativeOriginalFourResourceFunctional n v q x U K b C T P s star+
      nativeOriginalFourResourceFunctional n v q x U K b C T Q s star := by
  unfold nativeOriginalFourResourceFunctional
  dsimp only
  rw [nativeOriginalResourceChildFunctional_add,nativeOriginalResourceChildFunctional_add]
  ring

theorem nativeOriginalFourResourceFunctional_const_mul (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) (c : ℝ) :
    nativeOriginalFourResourceFunctional n v q x U K b C T (fun σ=>c*P σ) s star=
      c*nativeOriginalFourResourceFunctional n v q x U K b C T P s star := by
  unfold nativeOriginalFourResourceFunctional
  dsimp only
  rw [nativeOriginalResourceChildFunctional_const_mul n v q x U K b C _ ho,
    nativeOriginalResourceChildFunctional_const_mul n v q x U K b C _ ho]
  ring

theorem nativeOriginalClockGBranches_eq_child_functional
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) :
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let F:=nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockGBranchBeta U K b parent tag)
    ((nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      nativeActualOriginalGBranches weight st).map F).sum=
    (W⁻¹)^st.generation/(chi*K star)*nativeOriginalResourceChildFunctional n v q x U K b C
      st.tree (st.term.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀) st.term.live.test.target star := by
  dsimp only
  rw [nativeOriginalClockGBranches_response ho hs hU st K b C v₀ q₀ x₀ v q x W hW]
  unfold nativeOriginalResourceChildFunctional
  dsimp only
  simp only [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K]
  have Hsym : (fun σ c d=>st.term.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ*
        (deletedOverlap n (joinSpin d) (joinSpin c)-C star))=
      (fun σ c d=>st.term.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ*
        (deletedOverlap n (joinSpin c) (joinSpin d)-C star)) := by
    funext σ c d
    simp only [deletedOverlap,mul_comm]
  rw [Hsym]
  ring

theorem nativeOriginalClockFourGBranches_eq_functional
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) :
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let F:=nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
    ((nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      nativeActualOriginalFourGBranches weight st).map F).sum=
    (W⁻¹)^st.generation/(chi*K star)*nativeOriginalFourResourceFunctional n v q x U K b C
      st.tree (st.term.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀) st.term.live.test.target star := by
  dsimp only
  rw [nativeOriginalClockFourGBranches_eq_two_steps ho hs hU,
    nativeOriginalClockGBranches_eq_child_functional ho hs hU st K b C v₀ q₀ x₀ v q x W hW,
    nativeOriginalClockGBranches_eq_child_functional ho hs hU st.retarget K b C v₀ q₀ x₀ v q x W hW]
  simp only [NativeActualResourceState.retarget]
  have HV:=funext (fun σ=>st.term.retarget_value 0 (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀ σ)
  rw [HV]
  have HT : (st.term.retarget 0).live.test.target=
      (nativeFreshAtSlot st.tree 0 st.term.live.test.target star).mark := rfl
  rw [HT]
  unfold nativeOriginalFourResourceFunctional
  dsimp only
  ring

end OAI.SKFluctuations.Cavity
