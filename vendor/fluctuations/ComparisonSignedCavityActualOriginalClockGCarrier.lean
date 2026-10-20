module

public import ComparisonSignedCavityActualOriginalClockResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nativeOriginalClockHighStep_response
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (W : ℝ) :
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    ((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU) .highRow st).map
      (nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W)).sum=
    (W⁻¹)^(st.generation+1)*nativeOriginalFreshPartnerLResponse n v q x U K b C
      st.tree st.term.live.test.target star (fun σ c d=>F σ*(R d c-C star)) := by
  dsimp only
  unfold nativeActualResourceStep
  simp only [List.map_flatMap,native_sum_flatMap]
  unfold nativeOriginalFreshPartnerLResponse
  conv_rhs => rw [←List.sum_map_mul_left,←List.attach_map_val]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  split_ifs with hh
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      nativeOriginalClockStateResponse,NativeActualResourceState.markedRow]
    rw [nativeOriginalClockResourceResponse_reweight _ ho,
      nativeOriginalClockResourceResponse_markedSwitch st.term st.generation K b C
        v₀ q₀ x₀ v q x W p.val p.property hs hh]
    simp only [nativeOriginalHighRowGamma,NativeActualResourceState.toHigh]
    ring
  · simp only [List.map_nil,List.sum_nil]
    rw [fullScalarCutGamma_cross_zero p.val.tree ho U K _ _ hU (lt_of_not_ge hh)]
    ring

private theorem original_clock_G_weight_cancel (W chi K b L H : ℝ) (k : ℕ)
    (hW : W≠0) :
    (W*(chi*b/(chi*K)))*((W⁻¹)^(k+1)*L)+
      (W*(b/(chi*K)))*((W⁻¹)^(k+1)*H)=
    (W⁻¹)^k/(chi*K)*b*(chi*L+H) := by
  rw [pow_succ]
  calc
    (W*(chi*b/(chi*K)))*((W⁻¹)^k*W⁻¹*L)+
        (W*(b/(chi*K)))*((W⁻¹)^k*W⁻¹*H)=
        ((W⁻¹)^k/(chi*K)*b*(chi*L+H))*(W*W⁻¹) := by ring
    _=(W⁻¹)^k/(chi*K)*b*(chi*L+H) := by rw [mul_inv_cancel₀ hW,mul_one]

theorem nativeOriginalClockGBranches_response
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) :
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    let s:=st.term.live.test.target
    let g:=nativeFreshAtSlot st.tree 0 s star
    let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
    ((nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      nativeActualOriginalGBranches
      (fun parent tag=>nativeOriginalClockParentWeight W U K parent
        (nativeOriginalClockGBranchBeta U K b parent tag)) st).map
      (nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W)).sum=
    (W⁻¹)^st.generation/(chi*K star)*b star*
      (chi*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>F (g.restrict σ)*(R (st.tree.atSlot (g.restrict σ) s) (g.spin σ)-C star))
        (g.embed s)+nativeOriginalFreshPartnerLResponse n v q x U K b C st.tree s star
          (fun σ c d=>F σ*(R d c-C star))) := by
  dsimp only
  rw [nativeOriginalClockWeightedBranchStep_response ho]
  simp only [nativeActualOriginalGBranches,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,nativeActualResourceExpansion,List.flatMap_singleton']
  rw [nativeOriginalClockHighStep_response ho hs hU st K b C v₀ q₀ x₀ v q x W]
  simp only [nativeActualResourceStep,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,nativeOriginalClockStateResponse,NativeActualResourceState.projection]
  rw [nativeOriginalClockResourceResponse_projection st.term U st.generation K b C
    v₀ q₀ x₀ v q x W]
  unfold nativeOriginalClockParentWeight nativeOriginalClockGBranchBeta
  simp only [Nat.one_ne_zero,↓reduceIte,one_mul]
  exact original_clock_G_weight_cancel W _ _ _ _ _ st.generation hW

theorem nativeOriginalClockGCenteredBranches_response
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (hs : star < U) (hl : star ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (W : ℝ) :
    let Γ:=nativeOriginalHighRowGamma (n:=n) U K
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockGBranchBeta U K b parent tag)
    let children:=nativeActualWeightedBranchStep Γ hs hl nativeActualOriginalGBranches weight st
    let F:=nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W
    ((nativeActualWeightedBranchStep Γ hs hl nativeActualOriginalGCenteredBranches weight st).map F).sum=
      (children.map F).sum+(children.map (fun Q=>F Q.freeze)).sum := by
  dsimp only
  rw [nativeActualOriginalGCenteredBranches,nativeActualWeightedBranchStep_append_center]
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero]
  exact List.sum_map_add

end OAI.SKFluctuations.Cavity
