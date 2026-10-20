module

public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import SKProof.Port.ComparisonActualOriginalQRawResourcePairBudget
public import SKProof.Port.ComparisonActualOriginalQPullbackFourCutReadout
public import SKProof.Port.ComparisonActualOriginalQCavityCategoryInterfaces
public import SKProof.Port.ComparisonActualOriginalQInheritedCenteredDeletedSiteRate
public import ComparisonSignedCavityInheritedCenteredDeletedSiteRate

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {i star : ℕ}

def nativeActualOriginalCenteredResourceDeletedSite_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeActualOriginalOtherSourceCategory .deletedSite n q U b h K C st.tree
    (nativeOriginalCenteredRestTest n q U b h K st.tree
      (nativeActualResourceRestValue st.term 0 qfull 0 C)) st.term.live.test.target star

theorem native_actual_original_deleted_site_contrast_eq_retarget_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourOtherCategoryContrast_original_q M U st .deletedSite=
      nativeActualOriginalCenteredResourceDeletedSite_original_q M U st-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceDeletedSite_original_q M U st.retarget := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  unfold nativeActualOriginalFourOtherCategoryContrast_original_q nativeActualOriginalCenteredResourceDeletedSite_original_q
  dsimp only [NativeActualResourceState.retarget]
  change _=_-(1/2:ℝ)*nativeActualOriginalOtherSourceCategory .deletedSite n q U b h K C _
    (nativeOriginalCenteredRestTest n q U b h K _
      (nativeActualResourceRestValue (st.term.retarget 0) 0 qfull 0 C)) _ star
  rw [native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n q U b h K st.tree ho]
  rfl

theorem native_actual_original_deleted_site_contrast_abs_le_original_q
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star)
    (W B : ℝ)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceDeletedSite_original_q M U st| ≤ B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceDeletedSite_original_q M U st.retarget| ≤ B) :
    |(W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U st .deletedSite| ≤
      (3/2:ℝ)*B := by
  rw [native_actual_original_deleted_site_contrast_eq_retarget_original_q M U ho]
  rw [mul_sub,mul_left_comm ((W⁻¹)^st.generation) (1/2:ℝ)]
  apply (abs_sub _ _).trans
  have Hhalf : |(1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceDeletedSite_original_q M U st.retarget)|=
      (1/2:ℝ)*|(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceDeletedSite_original_q M U st.retarget|:=by
    rw [abs_mul];norm_num
  rw [Hhalf]
  linarith

end OAI.SKFluctuations.Cavity
