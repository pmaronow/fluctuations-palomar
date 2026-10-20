module

public import ComparisonSignedCavityActualOriginalGBranchCarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nativeActualOriginalGBranches_eq_two_forward_sub_resampling
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    let s:=st.term.live.test.target
    let g:=nativeFreshAtSlot st.tree 0 s star
    let A:=fun σ τ=>R σ τ-C star
    let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
    ((nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs
      (hs.le.trans hP.highCut_le_length) nativeActualOriginalGBranches
      (fun parent tag=>nativeActualParentRecursionWeight M W U parent
        (nativeActualOriginalGBranchBeta M U parent tag)) st).map
      (nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W)).sum=
    (W⁻¹)^st.generation/(chi*K star)*b star*
      (nativeOriginalConnectedLowForward n v q x U K b C g.tree (fun σ=>F (g.restrict σ))
        (g.embed s) g.mark A+
       nativeOriginalConnectedLowForward n v q x U K b C g.tree (fun σ=>F (g.restrict σ))
        g.mark (g.embed s) A-
       (chi/2)*nativeActualOriginalGProjectedResampling st.tree s star U K b C v q x A F) := by
  dsimp only
  rw [nativeActualOriginalGBranches_response M ho hs hP.highCut_le_length st
    v₀ q₀ x₀ v q x W hW]
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=finitePhysicalMixedClock (n+1) as b h
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
  let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
  let A:=fun σ τ=>R σ τ-C star
  have hR (σ τ : Spin n×Bool) : R σ τ=R τ σ := by
    dsimp only [R,deletedOverlap]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hA (σ τ : Spin n×Bool) : A σ τ=A τ σ := by
    dsimp only [A]
    rw [hR]
  have hK : ∀j,0 ≤ K j:=retainedStarMixedClock_nonneg n M.bf M.hf as
  have hKm : Monotone K:=retainedStarMixedClock_monotone n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HGa:=native_actual_generated_original_forward_G_eq_projection_add_resampling
    hP hi hs ho v q x K b C hq hq0 hK hKm A F
  have HGb:=native_original_fresh_forward_G_eq_partner_L_response n v q x U K b C
    st.tree ho st.term.live.test.target star hs hP.highCut_le_length hq hq0 hK hKm F A hA
  have HQ : (fun σ c d=>F σ*A c d)=(fun σ c d=>F σ*(R d c-C star)) := by
    funext σ c d
    dsimp only [A]
    rw [hR c d]
  rw [HQ] at HGb
  have Hchi:=native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K
    st.term.live.test.target
  rw [←Hchi] at HGa
  rw [HGa,HGb]
  ring

end OAI.SKFluctuations.Cavity
