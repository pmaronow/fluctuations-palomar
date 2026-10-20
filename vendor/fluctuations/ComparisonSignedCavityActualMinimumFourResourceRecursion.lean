module

public import ComparisonSignedCavityActualMinimumFourResourceSource
public import ComparisonSignedCavityActualFourGCentering

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem nativeOriginalClockStateResponse_centered_value
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (ho : MassOrdered 0 as)
    (U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let F:=st.term.value (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x
    (W⁻¹)^st.generation*nativeOriginalLongitudinalPairing n v q x U K b C st.tree
      (fun σ=>F σ-st.tree.disorderExpect (fullWeight n) (fullFeature n) v q F x)
      st.term.live.test.target=
    nativeOriginalClockStateResponse U K b C v q x v q x W st+
      nativeOriginalClockStateResponse U K b C v q x v q x W st.freeze := by
  dsimp only
  change _=nativeOriginalClockResourceResponse st.term U st.generation K b C v q x v q x W+
    nativeOriginalClockResourceResponse st.term.freeze U st.generation K b C v q x v q x W
  rw [nativeOriginalClockResourceResponse_freeze st.term ho]
  rw [native_original_longitudinal_centering]
  unfold nativeOriginalClockResourceResponse
  ring

theorem nativeOriginalClockFourGStepResponse_centered_value
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ} (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (W : ℝ) (hW : W≠0) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let F:=st.term.value (fullWeight n) (fullFeature n) v q
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x
    (W⁻¹)^st.generation/(chi*K star)*nativeOriginalFourResourceFunctional n v q x U K b C st.tree
      (fun σ=>F σ-st.tree.disorderExpect (fullWeight n) (fullFeature n) v q F x)
      st.term.live.test.target star=
    nativeOriginalClockFourGStepResponse hs hU K b C v q x v q x W st+
      nativeOriginalClockFourGStepResponse hs hU K b C v q x v q x W st.freeze := by
  dsimp only
  unfold nativeOriginalClockFourGStepResponse
  rw [nativeOriginalClockFourGBranches_eq_functional ho hs hU st K b C v q x v q x W hW,
    nativeOriginalClockFourGBranches_eq_functional ho hs hU st.freeze K b C v q x v q x W hW]
  let F:=st.term.value (fullWeight n) (fullFeature n) v q
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x
  have HV : (fun σ=>F σ-st.tree.disorderExpect (fullWeight n) (fullFeature n) v q F x)=
      fun σ=>F σ+st.term.freeze.value (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x σ := by
    funext σ
    rw [st.term.freeze_value (fullWeight_pos n) (fullFeature n) ho]
    rfl
  rw [HV,nativeOriginalFourResourceFunctional_add]
  change _=(W⁻¹)^st.generation/_*nativeOriginalFourResourceFunctional n v q x U K b C st.tree
    F st.term.live.test.target star+
    (W⁻¹)^st.generation/_*nativeOriginalFourResourceFunctional n v q x U K b C st.tree
      (st.term.freeze.value (fullWeight n) (fullFeature n) v q
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x) st.term.live.test.target star
  ring

def nativeActualOriginalFourResourceDefect
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

private theorem four_source_normalize (a d L D G : ℝ) (hd : d≠0)
    (H : d*L=D+G) : a*L=a/d*D+a/d*G := by
  calc
    a*L=(a/d)*(d*L) := by field_simp
    _=(a/d)*(D+G) := by rw [H]
    _=a/d*D+a/d*G := by ring

theorem actual_minimum_centered_resource_four_recursion
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W≠0)
    (hstarK : 0 < nativeContinuumMixedClock n M.bf M.hf as star) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let F:=nativeOriginalClockStateResponse U K b C 0 qfull 0 0 qfull 0 W
    let G:=nativeOriginalClockFourGStepResponse hs hP.highCut_le_length K b C 0 qfull 0 0 qfull 0 W
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    F st+F st.freeze=(W⁻¹)^st.generation/(chi*K star)*nativeActualOriginalFourResourceDefect M U st+
      G st+G st.freeze := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hchi : 0 < chi:=(Real.exp_pos _).trans_le Hchi.1
  have hd : chi*K star≠0:=(mul_pos hchi hstarK).ne'
  have Hsrc:=actual_minimum_centered_resource_four_source M st hP hi hs ho 0 qfull 0
  dsimp only at Hsrc
  have Hleft:=nativeOriginalClockStateResponse_centered_value ho U K b C 0 qfull 0 W st
  have Hright:=nativeOriginalClockFourGStepResponse_centered_value ho hs hP.highCut_le_length
    K b C 0 qfull 0 W hW st
  dsimp only at Hleft Hright
  rw [←Hleft,add_assoc,←Hright]
  apply four_source_normalize _ _ _ _ _ hd
  exact Hsrc

end OAI.SKFluctuations.Cavity
