module

public import ComparisonActualGeneralCenteredResourceLongitudinalRestoration
public import ComparisonActualGeneralFourCategories
public import ComparisonSignedCavityActualFourLongitudinalRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_general_four_longitudinal_contrast_eq_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as)
    (hstar : star ≤ as.length) (right : Bool) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    actualGeneralFourCategoryContrast bf hf U st (nativeActualLongitudinalCategory right)=
      -chi*K star*(actualGeneralOriginalFreshResourceLongitudinalRestoration bf hf U st.term right-
        (1/2:ℝ)*actualGeneralOriginalFreshResourceLongitudinalRestoration bf hf U (st.term.retarget 0) right) := by
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
  have hsplit (T : ClockTree (Spin n×Bool) as) (s : T.Slot) :
      (nativeFreshAtSlot T 0 s star).tree.splitIndex ((nativeFreshAtSlot T 0 s star).embed s)
        (nativeFreshAtSlot T 0 s star).mark=star:=by
    rw [ClockTree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hstar]
  cases right <;>
    unfold nativeActualLongitudinalCategory actualGeneralFourCategoryContrast
      nativeActualOriginalOtherSourceCategory actualGeneralOriginalFreshResourceLongitudinalRestoration <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,
      NativeGeneratedTest.retarget] <;>
    simp only [hsplit] <;> ring_nf <;> rfl

end OAI.SKFluctuations.Cavity
