module

public import ComparisonSignedCavityActualFourOtherSourceCategories
public import ComparisonSignedCavityActualFreshResourceJointHighRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem native_actual_four_joint_HIGH_restoration_contrast_eq_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) :
    nativeActualOriginalFourOtherCategoryContrast M U st kind.category=
      -(nativeActualOriginalFreshResourceJointHighRestoration kind M U st.term-
        (1/2:ℝ)*nativeActualOriginalFreshResourceJointHighRestoration kind M U (st.term.retarget 0)) := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  cases kind <;>
    unfold NativeJointHighRestorationKind.category nativeActualOriginalFourOtherCategoryContrast
      nativeActualOriginalOtherSourceCategory nativeActualOriginalFreshResourceJointHighRestoration
      nativeJointHighRestorationSource <;>
    dsimp only <;>
    rw [Hread] <;>
    dsimp only [b,h,K,C,q,NativeResourceTerm.retarget,NativeResourceMonomial.retarget,NativeGeneratedTest.retarget] <;>
    ring

end OAI.SKFluctuations.Cavity
