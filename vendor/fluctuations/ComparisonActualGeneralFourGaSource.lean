module

public import ComparisonActualGeneralFourGaReadout
public import ComparisonActualGeneralFourCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

theorem actual_general_four_Ga_contrast_eq_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (_hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (_hi : i ≤ star) (_hs : star < U) (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    actualGeneralFourGaContrast bf hf U st=
      (chi/2)*(bf (partitionPoint 0 as star):ℝ)*
        (actualGeneralResourceGa bf hf U st.term-
          (1/2:ℝ)*actualGeneralResourceGa bf hf U (st.term.retarget 0)) := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_general_resource_centered_Ga bf hf U st.term
  have H1:=actual_general_resource_centered_Ga bf hf U (st.term.retarget 0)
  dsimp only at H0 H1 ⊢
  change nativeActualOriginalGProjectedResampling g.tree g.mark star U K b C 0
      (cutFullVariance n q U 1 1 b h K) 0
      (fun σ τ=>restCenteredFixedForkKernel n b C star 0 σ.1 τ.1)
      (fun σ=>nativeOriginalCenteredRestTest n q U b h K g.tree
        (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C)
        (g.tree.cavityAssignment σ).1)=
    b star*actualGeneralResourceGa bf hf U (st.term.retarget 0) at H1
  rw [native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n q U b h K st.tree ho P st.term.live.test.target star] at H1
  unfold actualGeneralFourGaContrast nativeActualOriginalGaSource
  dsimp only
  rw [H0]
  rw [H1]
  ring

end OAI.SKFluctuations.Cavity
