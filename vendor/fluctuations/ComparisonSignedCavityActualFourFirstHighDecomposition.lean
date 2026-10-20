module

public import ComparisonSignedCavityActualFourFirstHighSource
public import ComparisonSignedCavityActualFourResidualDecomposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualOriginalFourOtherSourceErrorContrast
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

theorem actual_minimum_four_source_error_eq_first_high_add_other
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) :
    nativeActualOriginalFourSourceErrorContrast M U st=
      nativeActualOriginalFourFirstHighContrast M U st+
      nativeActualOriginalFourOtherSourceErrorContrast M U st := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_minimum_one_step_eq_first_high_add_other M hP hi hs ho Pc
  have H1:=actual_minimum_one_step_eq_first_high_add_other M hP.retarget hi hs ho
    (fun σ=>Pc (g.restRestrict σ))
  change nativeActualOriginalOneStepError n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star =
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      nativeGammaProjectedFirstHighDisplacement g.tree g.mark star U q b h K
        (restCenteredFixedForkKernel n b C star 0) (fun σ=>Pc (g.restRestrict σ))+
    nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star at H1
  unfold nativeActualOriginalFourSourceErrorContrast nativeActualOriginalFourFirstHighContrast
    nativeActualOriginalFourOtherSourceErrorContrast
  dsimp only at H0 H1 ⊢
  rw [H0,H1]
  ring

theorem actual_minimum_four_recursion_error_first_high_decomposition
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (hU : U≤as.length) (W : ℝ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourRecursionError M hs hU W st=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        ((W⁻¹)^st.generation*nativeActualOriginalFourPairContrast M U st)+
      nativeActualOriginalFourFirstHighError M U W st-
      (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourOtherSourceErrorContrast M U st)-
      nativeActualOriginalFourFrozenChildCorrection M hs hU W st := by
  rw [native_actual_original_four_recursion_error_decomposition,
    actual_minimum_four_source_error_eq_first_high_add_other M st hP hi hs ho]
  unfold nativeActualOriginalFourFirstHighError
  dsimp only
  ring

end OAI.SKFluctuations.Cavity
