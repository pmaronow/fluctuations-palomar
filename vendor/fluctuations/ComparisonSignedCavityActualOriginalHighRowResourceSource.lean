module

public import ComparisonSignedCavityActualOriginalForwardSourceAdapters
public import ComparisonSignedCavityActualFrozenResponseCarrier
public import ComparisonSignedCavityActualOriginalHighProfileRows
public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nativeActualResourceHighStep_eq_original_partner_response
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    ((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU) .highRow st).map
      (nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W)).sum=
    (W⁻¹)^(st.generation+1)*nativeOriginalFreshPartnerLResponse n v q x U K b C
      st.tree st.term.live.test.target star (fun σ c d=>F σ*(R d c-C star)) := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=finitePhysicalMixedClock (n+1) as b h
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
  unfold nativeActualResourceStep
  simp only [List.map_flatMap,native_sum_flatMap]
  unfold nativeOriginalFreshPartnerLResponse
  conv_rhs => rw [←List.sum_map_mul_left,←List.attach_map_val]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  split_ifs with hh
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      nativeActualFrozenResourceStateResponse]
    rw [nativeActualFrozenResourceResponse_markedRow M ho U v₀ q₀ x₀ v q x W st
      (nativeOriginalHighRowGamma U K) p.val p.property hs hh]
    rw [nativeActualFrozenResourceResponse_markedHighSwitch M st.term U st.generation
      v₀ q₀ x₀ v q x W p.val p.property hs hh]
    simp only [nativeOriginalHighRowGamma,NativeActualResourceState.toHigh]
    ring
  · simp only [List.map_nil,List.sum_nil]
    rw [fullScalarCutGamma_cross_zero p.val.tree ho U K _ _ hU (lt_of_not_ge hh)]
    ring

theorem nativeActualResourceHighStep_eq_original_G_source
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hq : ∀j,Monotone (fun k=>q k j)) (hq0 : ∀j,v j ≤ q 0 j) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    ((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU) .highRow st).map
      (nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W)).sum=
    (W⁻¹)^(st.generation+1)*nativeOriginalFreshPartnerGSource n v q x U K b C
      st.tree st.term.live.test.target star (fun σ c d=>F σ*(R d c-C star)) := by
  dsimp only
  rw [nativeActualResourceHighStep_eq_original_partner_response M ho hs hU st v₀ q₀ x₀ v q x W]
  erw [native_original_fresh_forward_G_source_eq_L_response n v q x U _ _ _ st.tree ho
    st.term.live.test.target star hs hU hq hq0
    (retainedStarMixedClock_nonneg n M.bf M.hf as)
    (retainedStarMixedClock_monotone n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho)]
  rfl

end OAI.SKFluctuations.Cavity
