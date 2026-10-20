module

public import ComparisonSignedCavityActualFourGLinearResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem nativeOriginalPairRecursionChildren_eq_functional (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) :
    nativeOriginalPairRecursionChildren n q U b h K C T P s star=
      nativeOriginalResourceChildFunctional n 0 (cutFullVariance n q U 1 1 b h K) 0
        U K b C T (fun σ=>P (T.cavityAssignment σ).1) s star := rfl

theorem actual_minimum_centered_resource_four_source
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let P:=nativeActualResourceRestValue st.term v₀ q₀ x₀ C
    let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀
    let Fc:=fun σ=>F σ-st.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull F 0
    let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
    let s:=st.term.live.test.target
    let g:=nativeFreshAtSlot st.tree 0 s star
    let Pg:=fun σ=>Pc (g.restRestrict σ)
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    chi*K star*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C st.tree Fc s=
      nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
      (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree Pg g.mark star+
      nativeOriginalFourResourceFunctional n 0 qfull 0 U K b C st.tree Fc s star := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term v₀ q₀ x₀ C
  let F:=st.term.value (fullWeight n) (fullFeature n) v₀ q₀
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C x₀
  let Fc:=fun σ=>F σ-st.tree.disorderExpect (fullWeight n) (fullFeature n) 0 qfull F 0
  let Pc:=nativeOriginalCenteredRestTest n qr U b h K st.tree P
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  have HQ : cutFullVariance n qr U 1 1 b h K=qfull:=
    native_full_endpoint_clock_mixed_independent n qr U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  have HF : (fun σ=>Pc (st.tree.cavityAssignment σ).1)=Fc := by
    have H:=native_actual_resource_original_centered_readout st.term v₀ q₀ x₀ C qr U b h K
    dsimp only at H
    rw [HQ] at H
    exact H
  have Hfresh : (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1))=
      fun σ=>Fc (g.restrict σ) := by
    funext σ
    rw [←g.restRestrict_actual]
    exact congrFun HF (g.restrict σ)
  have HE:=actual_minimum_original_longitudinal_eq_two_fresh_subtraction M hP hi hs ho P
  dsimp only at HE
  change _=nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star-
    nativeOriginalPairRecursionChildren n qr U b h K C st.tree Pc s star+
    (1/2:ℝ)*nativeOriginalPairRecursionChildren n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star at HE
  rw [nativeOriginalPairRecursionChildren_eq_functional,
    nativeOriginalPairRecursionChildren_eq_functional,HQ,HF,Hfresh] at HE
  change _=nativeOriginalPairRecursionDefect n qr U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeOriginalPairRecursionDefect n qr U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star+
    nativeOriginalFourResourceFunctional n 0 qfull 0 U K b C st.tree Fc s star
  unfold nativeOriginalFourResourceFunctional
  dsimp only
  linear_combination HE

end OAI.SKFluctuations.Cavity
