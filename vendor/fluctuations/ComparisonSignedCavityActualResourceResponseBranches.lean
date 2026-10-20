module

public import ComparisonSignedCavityActualResourceResponseOperations

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (U k : ℕ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ)

 theorem nativeActualFrozenResourceResponse_projection (hl : star≤as.length) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    nativeActualFrozenResourceResponse M (P.projection 0 k hl) U (k+1) v₀ q₀ x₀ v q x W=
      (W⁻¹)^(k+1)*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>F (g.restrict σ)*
          (R (T.atSlot (g.restrict σ) P.live.test.target) (g.spin σ)-C star))
        (g.embed P.live.test.target) := by
  dsimp only
  unfold nativeActualFrozenResourceResponse
  dsimp only
  have HV := funext (fun σ=>P.projection_value 0 k hl (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ)
  rw [HV]
  rfl

 theorem nativeActualFrozenResourceResponse_retarget :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    nativeActualFrozenResourceResponse M (P.retarget 0) U k v₀ q₀ x₀ v q x W=
      (W⁻¹)^k*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>F (g.restrict σ)) g.mark := by
  dsimp only
  unfold nativeActualFrozenResourceResponse
  dsimp only
  have HV := funext (fun σ=>P.retarget_value 0 (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ)
  rw [HV]
  rfl

 theorem nativeActualFrozenResourceResponse_markedHighSwitch
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hs : star<U) (hh : U≤p.tree.splitIndex (p.embed P.live.test.target) p.mark) :
    let g:=nativeFreshAtSlot p.tree 0 (p.embed P.live.test.target) star
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    nativeActualFrozenResourceResponse M (P.markedHighSwitch 0 k p hp hs hh)
      U (k+1) v₀ q₀ x₀ v q x W=
      (W⁻¹)^(k+1)*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>F (p.restrict (g.restrict σ))*(R (g.spin σ) (p.spin (g.restrict σ))-C star))
        g.mark := by
  dsimp only
  unfold nativeActualFrozenResourceResponse
  dsimp only
  have HV := funext (fun σ=>P.markedHighSwitch_value 0 k p hp hs hh
    (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ)
  rw [HV]
  rfl

include ho

 theorem nativeActualFrozenResourceResponse_freeze :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=P.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    nativeActualFrozenResourceResponse M P.freeze U k v₀ q₀ x₀ v q x W=
      -(W⁻¹)^k*T.disorderExpect (fullWeight n) (fullFeature n) v₀ q₀ F x₀*
        nativeOriginalLongitudinalPairing n v q x U K b C T (fun _=>1) P.live.test.target := by
  dsimp only
  unfold nativeActualFrozenResourceResponse
  dsimp only
  have HV := funext (fun σ=>P.freeze_value (fullWeight_pos n) (fullFeature n) ho v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.bf M.hf as) x₀ σ)
  rw [HV]
  let mean:=T.disorderExpect (fullWeight n) (fullFeature n) v₀ q₀
    (P.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.bf M.hf as) x₀) x₀
  have HF : (fun _ : T.Assignment=> -mean)=(fun _=> (-mean)*1) := by funext σ;ring
  change (W⁻¹)^k*nativeOriginalLongitudinalPairing n v q x U _ _ _ T (fun _=> -mean)
    P.live.test.target= -(W⁻¹)^k*mean*_
  rw [HF,native_original_longitudinal_const_mul_test n v q x U _ _ _ T ho]
  ring

 theorem nativeActualFrozenResourceResponse_markedRow
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as)→MarkedPlacement st.tree→ℝ)
    (p : MarkedPlacement st.tree) (hp : p∈st.tree.markedAttach 0)
    (hs : star<U) (hh : U≤p.tree.splitIndex (p.embed st.term.live.test.target) p.mark) :
    nativeActualFrozenResourceResponse M (st.markedRow Γ p hp hs hh).term U
      (st.markedRow Γ p hp hs hh).generation v₀ q₀ x₀ v q x W=
      (p.coeff*Γ st.toHigh p)*nativeActualFrozenResourceResponse M
        (st.term.markedHighSwitch 0 st.generation p hp hs hh) U (st.generation+1)
        v₀ q₀ x₀ v q x W := by
  exact nativeActualFrozenResourceResponse_reweight M _ ho U _ _ v₀ q₀ x₀ v q x W

end OAI.SKFluctuations.Cavity
