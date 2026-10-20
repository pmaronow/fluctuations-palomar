module

public import ComparisonActualGeneralFourFirstHighReadout
public import ComparisonActualGeneralFourCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

theorem actual_general_four_first_high_contrast_eq_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    actualGeneralFourFirstHighContrast bf hf U st=
      chi*(bf (partitionPoint 0 as star):ℝ)*
        (actualGeneralResourceFirstHigh bf hf U st.term-
          (1/2:ℝ)*actualGeneralResourceFirstHigh bf hf U (st.term.retarget 0)) := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_general_resource_centered_first_high bf hf hbf hhf hP hi hs ho
  have H1:=actual_general_resource_centered_first_high bf hf hbf hhf hP.retarget hi hs ho
  dsimp only at H0 H1 ⊢
  change nativeGammaProjectedFirstHighDisplacement g.tree g.mark star U q b h K
      (restCenteredFixedForkKernel n b C star 0)
      (nativeOriginalCenteredRestTest n q U b h K g.tree
        (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C))=
    b star*actualGeneralResourceFirstHigh bf hf U (st.term.retarget 0) at H1
  rw [native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n q U b h K st.tree ho P st.term.live.test.target star] at H1
  unfold actualGeneralFourFirstHighContrast
  dsimp only
  rw [H0]
  rw [H1]
  ring

end OAI.SKFluctuations.Cavity
