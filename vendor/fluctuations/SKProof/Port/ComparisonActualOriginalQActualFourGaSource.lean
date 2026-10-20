module

public import SKProof.Port.ComparisonActualOriginalQActualResourceGaReadout
public import ComparisonSignedCavityActualFourGaSource
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQActualFourGaReadout

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualOriginalFourGaContrast_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalGaSource n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalGaSource n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

theorem actual_minimum_four_Ga_contrast_eq_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (_hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (_hi : i ≤ star) (_hs : star < U) (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourGaContrast_original_q M U st=
      (chi/2)*(M.sweepBf (partitionPoint 0 as star):ℝ)*
        (nativeActualResourceGa_original_q M U st.term-
          (1/2:ℝ)*nativeActualResourceGa_original_q M U (st.term.retarget 0)) := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_minimum_resource_centered_Ga_original_q M U st.term
  have H1:=actual_minimum_resource_centered_Ga_original_q M U (st.term.retarget 0)
  dsimp only at H0 H1 ⊢
  change nativeActualOriginalGProjectedResampling g.tree g.mark star U K b C 0
      (cutFullVariance n q U 1 1 b h K) 0
      (fun σ τ=>restCenteredFixedForkKernel n b C star 0 σ.1 τ.1)
      (fun σ=>nativeOriginalCenteredRestTest n q U b h K g.tree
        (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C)
        (g.tree.cavityAssignment σ).1)=
    b star*nativeActualResourceGa_original_q M U (st.term.retarget 0) at H1
  rw [native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n q U b h K st.tree ho P st.term.live.test.target star] at H1
  unfold nativeActualOriginalFourGaContrast_original_q nativeActualOriginalGaSource
  dsimp only
  rw [H0]
  rw [H1]
  ring

def nativeActualOriginalFourGaError_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0;
  -((W⁻¹)^st.generation/(chi*K star))*nativeActualOriginalFourGaContrast_original_q M U st

theorem actual_minimum_four_Ga_error_eq_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (W : ℝ) :
    let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
    nativeActualOriginalFourGaError_original_q M U W st=
      -((M.sweepBf (partitionPoint 0 as star):ℝ)/(2*K star))*
        ((W⁻¹)^st.generation*nativeActualResourceGa_original_q M U st.term-
          (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGa_original_q M U (st.term.retarget 0))) := by
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hc : chi≠0:=ne_of_gt ((Real.exp_pos _).trans_le Hchi.1)
  unfold nativeActualOriginalFourGaError_original_q
  rw [actual_minimum_four_Ga_contrast_eq_resources_original_q M st hP hi hs ho]
  dsimp only
  change -((W⁻¹)^st.generation/(chi*K star))*
    ((chi/2)*(M.sweepBf (partitionPoint 0 as star):ℝ)*
      (nativeActualResourceGa_original_q M U st.term-
        (1/2:ℝ)*nativeActualResourceGa_original_q M U (st.term.retarget 0))) =
    -((M.sweepBf (partitionPoint 0 as star):ℝ)/(2*K star))*
      ((W⁻¹)^st.generation*nativeActualResourceGa_original_q M U st.term-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGa_original_q M U (st.term.retarget 0)))
  by_cases hk : K star=0
  · simp only [hk,mul_zero,div_zero,neg_zero,zero_mul]
  · field_simp [hc,hk]

end OAI.SKFluctuations.Cavity
