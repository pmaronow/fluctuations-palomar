module

public import ComparisonActualGeneralFourCategories
public import ComparisonActualGeneralCenteredResourceTransientLowReadout
public import ComparisonSignedCavityActualDeletedSiteReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

def actualGeneralOriginalResourceDeletedSiteSource
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeActualOriginalOtherSourceCategory .deletedSite n q U b h K C T Pc P.live.test.target star

theorem actual_general_original_deleted_site_source_eq_two_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let C:=nativePhysicalResourceCenter n bf hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    actualGeneralOriginalResourceDeletedSiteSource bf hf U P=
      -(nativeOriginalResourceSiteDeletedDifference (P.retarget 0) 0 qfull 0 U b h K C
        (g.embed P.live.test.target) g.mark+
        nativeOriginalResourceSiteDeletedDifference (P.retarget 0).freeze 0 qfull 0 U b h K C
        (g.embed P.live.test.target) g.mark) := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have H:=native_actual_original_deleted_site_eq_two_resources U b h K C T P ho
  dsimp only at H ⊢
  rw [HQ] at H
  exact H

theorem actual_general_four_deleted_site_contrast_eq_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) :
    actualGeneralFourCategoryContrast bf hf U st .deletedSite=
      actualGeneralOriginalResourceDeletedSiteSource bf hf U st.term-
        (1/2:ℝ)*actualGeneralOriginalResourceDeletedSiteSource bf hf U (st.term.retarget 0) := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold actualGeneralFourCategoryContrast actualGeneralOriginalResourceDeletedSiteSource
  dsimp only
  rw [Hread]
  rfl

end OAI.SKFluctuations.Cavity
