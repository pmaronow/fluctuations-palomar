module

public import ComparisonActualGeneralFourSource
public import ComparisonSignedCavityActualFreshPairEndpointMoment
public import ComparisonSignedCavityActualFourFreshPairContrast

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {as : List PositiveMass} {i star : ℕ}

def actualGeneralOriginalCenteredResourceFreshPair
    (bf hf : ℝ→ℝ≥0) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=cutFullVariance n qr U 1 1 b h K
  nativeActualOriginalFreshPairMoment n qr U b h K C st.tree
    (nativeOriginalCenteredRestTest n qr U b h K st.tree
      (nativeActualResourceRestValue st.term 0 qfull 0 C)) st.term.live.test.target star

theorem actual_general_four_pair_contrast_eq_retarget
    (bf hf : ℝ→ℝ≥0) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    actualGeneralFourPairContrast bf hf U st=
      actualGeneralOriginalCenteredResourceFreshPair bf hf U st-
        (1/2:ℝ)*actualGeneralOriginalCenteredResourceFreshPair bf hf U st.retarget := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n qr U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n qr U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  unfold actualGeneralFourPairContrast actualGeneralOriginalCenteredResourceFreshPair
  dsimp only [NativeActualResourceState.retarget]
  change _=_-(1/2:ℝ)*nativeActualOriginalFreshPairMoment n qr U b h K _ _
    (nativeOriginalCenteredRestTest n qr U b h K _
      (nativeActualResourceRestValue (st.term.retarget 0) 0 (cutFullVariance n qr U 1 1 b h K) 0 _))
      (st.term.retarget 0).live.test.target star
  rw [HQ,native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n qr U b h K st.tree ho]
  rfl

theorem actual_general_four_pair_contrast_abs_le
    (bf hf : ℝ→ℝ≥0) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star)
    (W B : ℝ)
    (Hparent : |(W⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair bf hf U st| ≤ B)
    (Hretarget : |(W⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair bf hf U st.retarget| ≤ B) :
    |(W⁻¹)^st.generation*actualGeneralFourPairContrast bf hf U st| ≤ (3/2:ℝ)*B := by
  rw [actual_general_four_pair_contrast_eq_retarget bf hf U ho]
  have Heq : (W⁻¹)^st.generation*
      (actualGeneralOriginalCenteredResourceFreshPair bf hf U st-
        (1/2:ℝ)*actualGeneralOriginalCenteredResourceFreshPair bf hf U st.retarget)=
      (W⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair bf hf U st+
        (-(1/2:ℝ))*((W⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair bf hf U st.retarget) := by ring
  rw [Heq]
  have H:=abs_add_le ((W⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair bf hf U st)
    ((-(1/2:ℝ))*((W⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair bf hf U st.retarget))
  have Hhalf : |(-(1/2:ℝ))*((W⁻¹)^st.generation*
      actualGeneralOriginalCenteredResourceFreshPair bf hf U st.retarget)|=
      (1/2:ℝ)*|(W⁻¹)^st.generation*actualGeneralOriginalCenteredResourceFreshPair bf hf U st.retarget| := by
    rw [abs_mul]
    norm_num
  rw [Hhalf] at H
  exact H.trans (by linarith [Hparent,Hretarget])

end OAI.SKFluctuations.Cavity
