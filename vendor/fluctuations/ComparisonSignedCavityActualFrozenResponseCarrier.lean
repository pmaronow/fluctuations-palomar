module

public import ComparisonSignedCavityActualResourceResponseBranches

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ}

 def nativeActualFrozenResourceStateResponse (U : ℕ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  nativeActualFrozenResourceResponse M st.term U st.generation v₀ q₀ x₀ v q x W

 theorem nativeActualWeightedBranchStep_frozen_response (ho : MassOrdered 0 as)
    (U : ℕ)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as)→MarkedPlacement st.tree→ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    ((nativeActualWeightedBranchStep Γ hs hl branches weight st).map
      (nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W)).sum=
      (branches.map (fun b=>weight st b.1*((nativeActualResourceExpansion Γ hs hl b.2 st).map
        (nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W)).sum)).sum := by
  unfold nativeActualWeightedBranchStep
  simp only [List.map_flatMap,native_sum_flatMap,List.map_map,Function.comp_def,
    nativeActualFrozenResourceStateResponse,NativeActualResourceState.reweight]
  simp_rw [nativeActualFrozenResourceResponse_reweight M _ ho]
  simp only [List.sum_map_mul_left]
  rfl

 theorem nativeActualWeightedBranchStep_parent_response (ho : MassOrdered 0 as)
    (U : ℕ)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) as)→MarkedPlacement st.tree→ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (hinc : ∀b∈branches,nativeActualExpansionMarkedCount b.2=1)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (beta : NativeActualResourceState (Spin n×Bool) as i star→ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) :
    let K:=retainedStarMixedClock n M.bf M.hf as
    let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
    ((nativeActualWeightedBranchStep Γ hs hl branches
      (fun Q tag=>nativeActualParentRecursionWeight M W U Q (beta Q tag)) st).map
      (nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W)).sum=
      (branches.map (fun b=>(beta st b.1/(chi*K star))*
        ((nativeActualResourceExpansion Γ hs hl b.2 st).map
          (fun Q=>nativeActualFrozenResourceResponse M Q.term U st.generation v₀ q₀ x₀ v q x W)).sum)).sum := by
  dsimp only
  unfold nativeActualWeightedBranchStep
  simp only [List.map_flatMap,native_sum_flatMap,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b hb
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro Q hQ
  have HD:=nativeActualResourceExpansion_generation Γ hs hl b.2 st Q hQ
  rw [hinc b hb] at HD
  change nativeActualFrozenResourceResponse M
    (Q.term.reweight (nativeActualParentRecursionWeight M W U st (beta st b.1))) U
    Q.generation v₀ q₀ x₀ v q x W=_
  rw [HD]
  exact nativeActualFrozenResourceResponse_weighted_successor M Q.term ho U st.generation _
    v₀ q₀ x₀ v q x W hW

end OAI.SKFluctuations.Cavity
