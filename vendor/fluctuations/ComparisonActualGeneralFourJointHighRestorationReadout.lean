module

public import ComparisonActualGeneralFreshResourceJointHighRestorationReadout
public import ComparisonActualGeneralFourCategories

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_general_four_joint_HIGH_restoration_contrast_eq_resources
    {n : ℕ} (kind : NativeJointHighRestorationKind) (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) :
    actualGeneralFourCategoryContrast bf hf U st kind.category=
      -(actualGeneralOriginalFreshResourceJointHighRestoration kind bf hf U st.term-
        (1/2:ℝ)*actualGeneralOriginalFreshResourceJointHighRestoration kind bf hf U (st.term.retarget 0)) := by
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
  cases kind <;>
    unfold NativeJointHighRestorationKind.category actualGeneralFourCategoryContrast
      nativeActualOriginalOtherSourceCategory actualGeneralOriginalFreshResourceJointHighRestoration
      nativeJointHighRestorationSource <;>
    dsimp only <;>
    rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,NativeGeneratedTest.retarget] <;>
    ring

end OAI.SKFluctuations.Cavity
