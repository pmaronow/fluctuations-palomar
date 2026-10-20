module

public import ComparisonSignedCavityActualOriginalHighRowResourceSource
public import ComparisonSignedCavityActualOriginalProjectionResampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeActualOriginalGBranches : NativeActualWeightedBranches :=
  [(0,[.projection]),(1,[.highRow])]

def nativeActualOriginalGBranchBeta
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) : ℝ :=
  let K:=retainedStarMixedClock n M.bf M.hf as
  let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
  (if tag=0 then chi else 1)*(M.bf (partitionPoint 0 as star):ℝ)

private theorem original_G_branch_weight_cancel (W chi K b L H : ℝ) (k : ℕ)
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

theorem nativeActualOriginalGBranches_response
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=finitePhysicalMixedClock (n+1) as b h
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let R:=fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀ R C x₀
    let s:=st.term.live.test.target
    let g:=nativeFreshAtSlot st.tree 0 s star
    let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
    ((nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      nativeActualOriginalGBranches
      (fun parent tag=>nativeActualParentRecursionWeight M W U parent
        (nativeActualOriginalGBranchBeta M U parent tag)) st).map
      (nativeActualFrozenResourceStateResponse M U v₀ q₀ x₀ v q x W)).sum=
    (W⁻¹)^st.generation/(chi*K star)*b star*
      (chi*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>F (g.restrict σ)*(R (st.tree.atSlot (g.restrict σ) s) (g.spin σ)-C star))
        (g.embed s)+nativeOriginalFreshPartnerLResponse n v q x U K b C st.tree s star
          (fun σ c d=>F σ*(R d c-C star))) := by
  dsimp only
  rw [nativeActualWeightedBranchStep_frozen_response M ho]
  simp only [nativeActualOriginalGBranches,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,nativeActualResourceExpansion,List.flatMap_singleton']
  rw [nativeActualResourceHighStep_eq_original_partner_response M ho hs hU st
    v₀ q₀ x₀ v q x W]
  simp only [nativeActualResourceStep,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,nativeActualFrozenResourceStateResponse,NativeActualResourceState.projection]
  rw [nativeActualFrozenResourceResponse_projection M st.term U st.generation
    v₀ q₀ x₀ v q x W]
  unfold nativeActualParentRecursionWeight nativeActualOriginalGBranchBeta
  simp only [retainedStarMixedClock,Nat.one_ne_zero,↓reduceIte,one_mul]
  exact original_G_branch_weight_cancel W _ _ _ _ _ st.generation hW

end OAI.SKFluctuations.Cavity
