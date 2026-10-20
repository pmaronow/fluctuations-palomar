module

public import ComparisonSignedCavityActualFirstHighSourceSplit
public import ComparisonSignedCavityActualMinimumFourResourceRecursion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualOriginalFourFirstHighContrast
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
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*(nativeGammaProjectedFirstHighDisplacement st.tree s star U q b h K
      (restCenteredFixedForkKernel n b C star 0) Pc-
    (1/2:ℝ)*nativeGammaProjectedFirstHighDisplacement g.tree g.mark star U q b h K
      (restCenteredFixedForkKernel n b C star 0) (fun σ=>Pc (g.restRestrict σ)))

theorem actual_minimum_four_first_high_contrast_eq_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalFourFirstHighContrast M U st=
      chi*(M.bf (partitionPoint 0 as star):ℝ)*
        (nativeActualResourceFirstHigh M U st.term-
          (1/2:ℝ)*nativeActualResourceFirstHigh M U (st.term.retarget 0)) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let P:=nativeActualResourceRestValue st.term 0 qfull 0 C
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_minimum_resource_centered_first_high M hP hi hs ho
  have H1:=actual_minimum_resource_centered_first_high M hP.retarget hi hs ho
  dsimp only at H0 H1 ⊢
  change nativeGammaProjectedFirstHighDisplacement g.tree g.mark star U q b h K
      (restCenteredFixedForkKernel n b C star 0)
      (nativeOriginalCenteredRestTest n q U b h K g.tree
        (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C))=
    b star*nativeActualResourceFirstHigh M U (st.term.retarget 0) at H1
  rw [native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n q U b h K st.tree ho P st.term.live.test.target star] at H1
  unfold nativeActualOriginalFourFirstHighContrast
  dsimp only
  rw [H0]
  rw [H1]
  ring

def nativeActualOriginalFourFirstHighError
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0;
  -((W⁻¹)^st.generation/(chi*K star))*nativeActualOriginalFourFirstHighContrast M U st

theorem actual_minimum_four_first_high_error_eq_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (W : ℝ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    nativeActualOriginalFourFirstHighError M U W st=
      -((M.bf (partitionPoint 0 as star):ℝ)/K star)*
        ((W⁻¹)^st.generation*nativeActualResourceFirstHigh M U st.term-
          (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceFirstHigh M U (st.term.retarget 0))) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hc : chi≠0:=ne_of_gt ((Real.exp_pos _).trans_le Hchi.1)
  unfold nativeActualOriginalFourFirstHighError
  rw [actual_minimum_four_first_high_contrast_eq_resources M st hP hi hs ho]
  dsimp only
  change -((W⁻¹)^st.generation/(chi*K star))*
    (chi*(M.bf (partitionPoint 0 as star):ℝ)*
      (nativeActualResourceFirstHigh M U st.term-
        (1/2:ℝ)*nativeActualResourceFirstHigh M U (st.term.retarget 0))) =
    -((M.bf (partitionPoint 0 as star):ℝ)/K star)*
      ((W⁻¹)^st.generation*nativeActualResourceFirstHigh M U st.term-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceFirstHigh M U (st.term.retarget 0)))
  by_cases hk : K star=0
  · simp only [hk,mul_zero,div_zero,neg_zero,zero_mul]
  · field_simp [hc,hk]

end OAI.SKFluctuations.Cavity
