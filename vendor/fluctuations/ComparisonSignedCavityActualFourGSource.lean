module

public import ComparisonSignedCavityActualFourGBranches
public import ComparisonSignedCavityActualOriginalClockGCarrier
public import ComparisonSignedCavityActualMinimumTwoFreshRecursion
public import ComparisonSignedCavityActualResourceRestReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem nativeOriginalClockFourGBranches_eq_two_steps
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b C : ℕ→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) :
    let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
    let F:=nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ v q x W
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockGBranchBeta U K b parent tag)
    let weight4:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)
    ((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
      nativeActualOriginalFourGBranches weight4 st).map F).sum=
      -((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalGBranches weight st).map F).sum+
      (1/2:ℝ)*((nativeActualWeightedBranchStep Γ hs (hs.le.trans hU)
        nativeActualOriginalGBranches weight st.retarget).map F).sum := by
  dsimp only
  rw [nativeOriginalClockWeightedBranchStep_response ho,
    nativeOriginalClockWeightedBranchStep_response ho,
    nativeOriginalClockWeightedBranchStep_response ho]
  simp only [nativeActualOriginalFourGBranches,nativeActualOriginalGBranches,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    nativeActualResourceExpansion,List.flatMap_singleton']
  simp only [nativeActualResourceStep,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  unfold nativeOriginalClockParentWeight nativeOriginalClockFourGBranchBeta
    nativeOriginalClockGBranchBeta
  simp only [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K,
    native_full_gamma_row_hessian n st.retarget.tree ho 0 ho U (by omega) K]
  norm_num only [Nat.reduceLT,↓reduceIte,Nat.reduceSub,Nat.one_ne_zero]
  ring

theorem nativeOriginalClockGBranches_eq_resource_children
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (K b h C : ℕ→ℝ)
    (q : ℕ→RestCoordinate n→ℝ)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) :
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let qfull:=cutFullVariance n q U 1 1 b h K
    let F:=nativeOriginalClockStateResponse U K b C v₀ q₀ x₀ 0 qfull 0 W
    let weight:=fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockGBranchBeta U K b parent tag)
    ((nativeActualWeightedBranchStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
      nativeActualOriginalGBranches weight st).map F).sum=
    (W⁻¹)^st.generation/(chi*K star)*
      nativeOriginalPairRecursionChildren n q U b h K C st.tree
        (nativeActualResourceRestValue st.term v₀ q₀ x₀ C) st.term.live.test.target star := by
  dsimp only
  rw [nativeOriginalClockGBranches_response ho hs hU st K b C v₀ q₀ x₀
    0 (cutFullVariance n q U 1 1 b h K) 0 W hW]
  unfold nativeOriginalPairRecursionChildren
  dsimp only
  simp only [native_actual_resource_rest_value_eq_full]
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

end OAI.SKFluctuations.Cavity
