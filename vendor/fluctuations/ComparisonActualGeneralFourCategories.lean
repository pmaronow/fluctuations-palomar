module

public import ComparisonActualGeneralFourSource
public import ComparisonSignedCavityActualFourOtherSourceCategories
public import ComparisonSignedCavityActualFourForestNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

def actualGeneralFourCategoryContrast
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (cat : NativeActualOtherSourceCategory) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOtherSourceCategory cat n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOtherSourceCategory cat n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def actualGeneralFourOtherSourceErrorContrast
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def actualGeneralFourGaContrast
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let s:=st.term.live.test.target
  let g:=nativeFreshAtSlot st.tree 0 s star
  nativeActualOriginalGaSource n q U b h K C st.tree Pc s star-
    (1/2:ℝ)*nativeActualOriginalGaSource n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star

def actualGeneralFourFirstHighContrast
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
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

def actualGeneralFourCategorySum
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    (cat : NativeActualOtherSourceCategory) : ℝ :=
  (rows.map (fun Q=>(W⁻¹)^Q.generation*actualGeneralFourCategoryContrast bf hf U Q cat)).sum

def actualGeneralFourCategoryError
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (Q : NativeActualResourceState (Spin n×Bool) as i star)
    (cat : NativeActualOtherSourceCategory) : ℝ :=
  let K:=nativeContinuumMixedClock n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1/(chi*K star))*((W⁻¹)^Q.generation*actualGeneralFourCategoryContrast bf hf U Q cat)

theorem actual_general_four_other_source_eq_Ga_add_categories
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (U : ℕ)
    {as : List PositiveMass} {i star : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star) :
    actualGeneralFourOtherSourceErrorContrast bf hf U st=
      actualGeneralFourGaContrast bf hf U st+
      (nativeActualOtherSourceCategories.map
        (actualGeneralFourCategoryContrast bf hf U st)).sum := by
  unfold actualGeneralFourOtherSourceErrorContrast actualGeneralFourGaContrast actualGeneralFourCategoryContrast
  dsimp only
  rw [native_actual_other_source_eq_Ga_add_categories,native_actual_other_source_eq_Ga_add_categories]
  simp only [nativeActualOtherSourceCategories,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

theorem actual_general_four_other_source_sum_eq_Ga_add_categories
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    (rows.map (fun Q=>(W⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q)).sum=
      (rows.map (fun Q=>(W⁻¹)^Q.generation*actualGeneralFourGaContrast bf hf U Q)).sum+
      (nativeActualOtherSourceCategories.map (actualGeneralFourCategorySum bf hf U W rows)).sum := by
  induction rows with
  | nil=>simp [actualGeneralFourCategorySum,nativeActualOtherSourceCategories]
  | cons Q rows ih=>
    simp only [List.map_cons,List.sum_cons] at ih ⊢
    rw [actual_general_four_other_source_eq_Ga_add_categories,ih]
    simp only [actualGeneralFourCategorySum,nativeActualOtherSourceCategories,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring

theorem actual_general_four_category_signed_sum_abs_le_error_sum
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    {as : List PositiveMass} {i star : ℕ}
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    (cat : NativeActualOtherSourceCategory)
    (hden : 0 < (scalarTerminal.schedule
      (scalarBoundaryClocks as (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0*
        nativeContinuumMixedClock n bf hf as star) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |actualGeneralFourCategorySum bf hf U W rows cat|/(chi*K star) ≤
      (rows.map (fun Q=>|actualGeneralFourCategoryError bf hf U W Q cat|)).sum := by
  have H:=native_abs_sum_map_le rows (fun Q=>actualGeneralFourCategoryError bf hf U W Q cat)
  unfold actualGeneralFourCategoryError at H
  dsimp only at H ⊢
  rw [List.sum_map_mul_left,abs_mul,abs_of_pos (div_pos zero_lt_one hden)] at H
  simpa only [actualGeneralFourCategorySum,actualGeneralFourCategoryError,
    one_div,one_mul,mul_comm,div_eq_mul_inv] using H

theorem actual_general_one_step_eq_first_high_add_other
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) (P : T.cavityLeft.Assignment→ℝ) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    nativeActualOriginalOneStepError n q U b h K C T P P₀.live.test.target star=
      chi*nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K
        (restCenteredFixedForkKernel n b C star 0) P+
      nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C T P P₀.live.test.target star := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hbf hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hhf hu hv huv)) as ho
  apply native_original_one_step_eq_first_high_add_other hP hi hs ho
  · intro j i
    cases i <;> exact NNReal.coe_nonneg _
  · intro i
    cases i
    · exact hbm
    · exact hhm
  · exact fun j=>NNReal.coe_nonneg _
  · exact fun j=>NNReal.coe_nonneg _
  · exact native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  · exact hbm
  · exact hhm
  · exact native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho

theorem actual_general_four_source_error_eq_first_high_add_other
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) :
    actualGeneralFourSourceErrorContrast bf hf U st=
      actualGeneralFourFirstHighContrast bf hf U st+
      actualGeneralFourOtherSourceErrorContrast bf hf U st := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K st.tree
    (nativeActualResourceRestValue st.term 0 qfull 0 C)
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=actual_general_one_step_eq_first_high_add_other bf hf hbf hhf hP hi hs ho Pc
  have H1:=actual_general_one_step_eq_first_high_add_other bf hf hbf hhf hP.retarget hi hs ho
    (fun σ=>Pc (g.restRestrict σ))
  change nativeActualOriginalOneStepError n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star =
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      nativeGammaProjectedFirstHighDisplacement g.tree g.mark star U q b h K
        (restCenteredFixedForkKernel n b C star 0) (fun σ=>Pc (g.restRestrict σ))+
    nativeActualOriginalOneStepWithoutFirstHigh n q U b h K C g.tree
      (fun σ=>Pc (g.restRestrict σ)) g.mark star at H1
  unfold actualGeneralFourSourceErrorContrast actualGeneralFourFirstHighContrast
    actualGeneralFourOtherSourceErrorContrast
  dsimp only at H0 H1 ⊢
  rw [H0,H1]
  ring

end OAI.SKFluctuations.Cavity
