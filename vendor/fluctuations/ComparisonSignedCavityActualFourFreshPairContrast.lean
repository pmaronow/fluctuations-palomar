module

public import ComparisonSignedCavityActualFourResidualDecomposition
public import ComparisonSignedCavityActualFourFirstHighReadout
public import ComparisonSignedCavityActualConstantFreshPairFeedback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star : ℕ}

def nativeActualOriginalCenteredResourceFreshPair
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=cutFullVariance n qr U 1 1 b h K
  nativeActualOriginalFreshPairMoment n qr U b h K C st.tree
    (nativeOriginalCenteredRestTest n qr U b h K st.tree
      (nativeActualResourceRestValue st.term 0 qfull 0 C)) st.term.live.test.target star

theorem native_actual_original_four_pair_contrast_eq_retarget
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star) :
    nativeActualOriginalFourPairContrast M U st=
      nativeActualOriginalCenteredResourceFreshPair M U st-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceFreshPair M U st.retarget := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let qr : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n qr U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n qr U 1 b h K
      (finitePhysicalMixedClock (n+1) as b h)
  unfold nativeActualOriginalFourPairContrast nativeActualOriginalCenteredResourceFreshPair
  dsimp only [NativeActualResourceState.retarget]
  change _=_-(1/2:ℝ)*nativeActualOriginalFreshPairMoment n qr U b h K _ _
    (nativeOriginalCenteredRestTest n qr U b h K _
      (nativeActualResourceRestValue (st.term.retarget 0) 0 (cutFullVariance n qr U 1 1 b h K) 0 _))
      (st.term.retarget 0).live.test.target star
  rw [HQ,native_actual_resource_rest_value_retarget,
    native_original_centered_rest_test_fresh n qr U b h K st.tree ho]
  rfl

theorem native_actual_original_four_pair_contrast_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ)
    (ho : MassOrdered 0 as) (st : NativeActualResourceState (Spin n×Bool) as i star)
    (W B : ℝ)
    (Hparent : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair M U st| ≤ B)
    (Hretarget : |(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair M U st.retarget| ≤ B) :
    |(W⁻¹)^st.generation*nativeActualOriginalFourPairContrast M U st| ≤ (3/2:ℝ)*B := by
  rw [native_actual_original_four_pair_contrast_eq_retarget M U ho]
  have Heq : (W⁻¹)^st.generation*
      (nativeActualOriginalCenteredResourceFreshPair M U st-
        (1/2:ℝ)*nativeActualOriginalCenteredResourceFreshPair M U st.retarget)=
      (W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair M U st+
        (-(1/2:ℝ))*((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair M U st.retarget) := by ring
  rw [Heq]
  have H:=abs_add_le ((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair M U st)
    ((-(1/2:ℝ))*((W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair M U st.retarget))
  have Hhalf : |(-(1/2:ℝ))*((W⁻¹)^st.generation*
      nativeActualOriginalCenteredResourceFreshPair M U st.retarget)|=
      (1/2:ℝ)*|(W⁻¹)^st.generation*nativeActualOriginalCenteredResourceFreshPair M U st.retarget| := by
    rw [abs_mul]
    norm_num
  rw [Hhalf] at H
  exact H.trans (by linarith [Hparent,Hretarget])

def ActualOriginalFourPairContrastSavingOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (A gamma sharpSaving Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→(∀u∈uniformMasses Lnet,u∈us)→
    ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i k : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [.initial] k T P→1+k ≤ degree→
        i ≤ star→star < U→U ≤ as.length→
      ∀x : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as i ≤ Cmass*x→
        |((W n)⁻¹)^k*nativeActualOriginalFourPairContrast (M n) U ⟨T,P,k⟩| ≤
          3*|P.coefficient| *A^(1+k)*x*(((n+1:ℕ):ℝ)^(-gamma))^k*
            (((n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))

theorem actual_original_four_pair_contrast_saving_of_fresh_feedback
    {m delta cl cu Az C0 Ct D Bclock gamma sharpSaving Cmass : ℝ} (degree : ℕ) (A : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hfresh : ActualOriginalFreshPairResourceSavingOnEveryFinalNet degree A gamma sharpSaving Cmass M W w) :
    ActualOriginalFourPairContrastSavingOnEveryFinalNet degree A gamma sharpSaving Cmass M W w := by
  filter_upwards [Hfresh] with n hn
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hn Lnet us hus hstar hret hmesh] with j hj
  dsimp only at hj ⊢
  intro U i k T P hP hdegree hi hs hU x hxsx hxW hmass
  have H0:=hj U i k T P hP hdegree hi hs hU x hxsx hxW hmass
  have H1:=hj U i k _ (P.retarget 0) hP.retarget hdegree hi hs hU x hxsx hxW hmass
  have H:=native_actual_original_four_pair_contrast_abs_le (M n) U
    (finiteCutMasses_ordered us hus j) ⟨T,P,k⟩ (W n) _ H0 H1
  convert H using 1
  ring

def ActualOriginalConstantFourPairContrastSavingOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (gamma sharpSaving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i k : ℕ) (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [] k T P→k ≤ degree→
        i ≤ star→star < U→U ≤ as.length→
        |((W n)⁻¹)^k*nativeActualOriginalFourPairContrast (M n) U ⟨T,P,k⟩| ≤
          3*|P.coefficient| *(((n+1:ℕ):ℝ)^(-gamma))^k*
            (((n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))

theorem actual_original_constant_four_pair_contrast_saving_of_fresh_feedback
    {m delta cl cu Az C0 Ct D Bclock gamma sharpSaving : ℝ} (degree : ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hfresh : ActualOriginalConstantFreshPairSavingOnEveryFinalNet degree gamma sharpSaving M W w) :
    ActualOriginalConstantFourPairContrastSavingOnEveryFinalNet degree gamma sharpSaving M W w := by
  filter_upwards [Hfresh] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U i k T P hP hdegree hi hs hU
  have H0:=hj U i k T P hP hdegree hi hs hU
  have H1:=hj U i k _ (P.retarget 0) hP.retarget hdegree hi hs hU
  have H:=native_actual_original_four_pair_contrast_abs_le (M n) U
    (finiteCutMasses_ordered us hus j) ⟨T,P,k⟩ (W n) _ H0 H1
  convert H using 1
  ring

end OAI.SKFluctuations.Cavity
