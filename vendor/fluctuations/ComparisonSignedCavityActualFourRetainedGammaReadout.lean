module

public import ComparisonSignedCavityActualRetainedGammaProjectedReadout
public import ComparisonSignedCavityActualFourOtherSourceCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def nativeActualResourceRetainedGammaRow
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {i : ℕ} (U : ℕ) (V : ℝ) (P : NativeResourceTerm i (pre.length+mid.length) T) : ℝ :=
  nativeActualResourceOriginalScalar M U P*
    nativeResetProjectedGammaRow n T P.live.test M U V
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 (pre++(mid++tail)) j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 (pre++(mid++tail)) j):ℝ)))
      (nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail))) 0
      (nativePhysicalResourceCenter n M.bf M.hf (pre++(mid++tail)) (pre.length+mid.length))

theorem actual_minimum_resource_centered_retained_gamma_eq_projected_row
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {i U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed k T P)
    (hi : i≤pre.length+mid.length) (hs : pre.length+mid.length<U)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    let as:=pre++(mid++tail)
    let star:=pre.length+mid.length
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeRetainedGammaProjectedDisplacement T P.live.test.target star U q K
      (restCenteredFixedForkKernel n b C star 0) Pc=
      (-b star/2)*nativeActualResourceRetainedGammaRow M U V P := by
  dsimp only
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  have H:=native_actual_generated_retained_gamma_affine_eq_reset_row (pre:=pre) (mid:=mid) (tail:=tail) hP hi hs M ho V hV q K
    (nativeActualResourceOriginalScalar M U P)
    (nativeOriginalRestTestExpectation n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))
    (b star) (C star)
  dsimp only at H
  have HR : (fun u v : Spin n=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))=
      fun u v=>(∑j,spinValue (u j)*spinValue (v j))/(n+1:ℕ) := by
    funext u v
    simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  rw [HR] at H
  have HRpoint (u v : Spin n):=congrFun (congrFun HR u) v
  simp only [HRpoint] at H
  have Hscalar : nativeActualResourceOriginalScalar M U P=
      P.scalar (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 := rfl
  rw [Hscalar] at H
  have Hkernel : (fun u v=>b star*((∑j,spinValue (u j)*spinValue (v j))/(n+1:ℕ)-C star))=
      restCenteredFixedForkKernel n b C star 0 := rfl
  change nativeRetainedGammaProjectedDisplacement T P.live.test.target star U q K
      (fun u v=>b star*((∑j,spinValue (u j)*spinValue (v j))/(n+1:ℕ)-C star))
      (nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C))=
      (-b star*(nativeActualResourceOriginalScalar M U P)/2)*
        nativeResetProjectedGammaRow n T P.live.test M U V q K 0 (C star) at H
  rw [Hkernel] at H
  exact H.trans (by
    change (-b star*nativeActualResourceOriginalScalar M U P/2)*
      nativeResetProjectedGammaRow n T P.live.test M U V q K 0 (C star)=
      (-b star/2)*(nativeActualResourceOriginalScalar M U P*
        nativeResetProjectedGammaRow n T P.live.test M U V q K 0 (C star))
    ring)

theorem actual_minimum_four_retained_gamma_category_eq_projected_rows
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {i U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) i (pre.length+mid.length))
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed st.generation st.tree st.term)
    (hi : i≤pre.length+mid.length) (hs : pre.length+mid.length<U)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    let as:=pre++(mid++tail)
    let star:=pre.length+mid.length
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourOtherCategoryContrast M U st .gammaRetained=
      (-chi*(M.bf (partitionPoint 0 as star):ℝ)/2)*
        (nativeActualResourceRetainedGammaRow M U V st.term-
          (1/2:ℝ)*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0)) := by
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_minimum_resource_centered_retained_gamma_eq_projected_row (pre:=pre) (mid:=mid) (tail:=tail) M hP hi hs ho V hV
  have H1:=actual_minimum_resource_centered_retained_gamma_eq_projected_row (pre:=pre) (mid:=mid) (tail:=tail) M hP.retarget hi hs ho V hV
  dsimp only at H0 H1 ⊢
  change nativeRetainedGammaProjectedDisplacement g.tree g.mark star U q K
      (restCenteredFixedForkKernel n b C star 0)
      (nativeOriginalCenteredRestTest n q U b h K g.tree
        (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C))=
    (-b star/2)*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0) at H1
  rw [native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n q U b h K st.tree ho P st.term.live.test.target star] at H1
  unfold nativeActualOriginalFourOtherCategoryContrast nativeActualOriginalOtherSourceCategory
  dsimp only
  rw [H0,H1]
  ring

end OAI.SKFluctuations.Cavity
