module

public import SKProof.Port.ComparisonActualOriginalQSquareResourceConsumerCore
public import ComparisonSignedCavityActualFourFreshPairContrastAlong
public import SKProof.Port.ComparisonActualOriginalQSquareConsumerActualConstantFreshPairFeedbackAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum (ActualSlowWindowChoice)
set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
def ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (A gamma sharpSaving Cmass : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→(∀u∈uniformMasses Lnet,u∈us)→
    ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [.initial] k T P→1+k ≤ degree→
        i ≤ star→star < U→U ≤ as.length→
      ∀x : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as i ≤ Cmass*x→
        |((W n)⁻¹)^k*nativeActualOriginalFourPairContrast_original_q (M n) U ⟨T,P,k⟩| ≤
          3*|P.coefficient| *A^(1+k)*x*(((dim n+1:ℕ):ℝ)^(-gamma))^k*
            (((dim n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))

theorem actual_original_four_pair_contrast_saving_of_fresh_feedback_along_original_q
    {m delta cl cu Az C0 Ct D Bclock gamma sharpSaving Cmass : ℝ} (degree : ℕ) (A : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hfresh : ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong_original_q degree A gamma sharpSaving Cmass M W w) :
    ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong_original_q degree A gamma sharpSaving Cmass M W w := by
  filter_upwards [Hfresh] with n hn
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hn Lnet us hus hstar hret hmesh] with j hj
  dsimp only at hj ⊢
  intro U i k T P hP hdegree hi hs hU x hxsx hxW hmass
  have H0:=hj U i k T P hP hdegree hi hs hU x hxsx hxW hmass
  have H1:=hj U i k _ (P.retarget 0) hP.retarget hdegree hi hs hU x hxsx hxW hmass
  have H:=native_actual_original_four_pair_contrast_abs_le_original_q (M n) U
    (finiteCutMasses_ordered us hus j) ⟨T,P,k⟩ (W n) _ H0 H1
  convert H using 1
  ring

def ActualOriginalConstantFourPairContrastSavingOnEveryFinalNetAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (degree : ℕ) (gamma sharpSaving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [] k T P→k ≤ degree→
        i ≤ star→star < U→U ≤ as.length→
        |((W n)⁻¹)^k*nativeActualOriginalFourPairContrast_original_q (M n) U ⟨T,P,k⟩| ≤
          3*|P.coefficient| *(((dim n+1:ℕ):ℝ)^(-gamma))^k*
            (((dim n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))

theorem actual_original_constant_four_pair_contrast_saving_of_fresh_feedback_along_original_q
    {m delta cl cu Az C0 Ct D Bclock gamma sharpSaving : ℝ} (degree : ℕ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hfresh : ActualOriginalConstantFreshPairSavingOnEveryFinalNetAlong_original_q degree gamma sharpSaving M W w) :
    ActualOriginalConstantFourPairContrastSavingOnEveryFinalNetAlong_original_q degree gamma sharpSaving M W w := by
  filter_upwards [Hfresh] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U i k T P hP hdegree hi hs hU
  have H0:=hj U i k T P hP hdegree hi hs hU
  have H1:=hj U i k _ (P.retarget 0) hP.retarget hdegree hi hs hU
  have H:=native_actual_original_four_pair_contrast_abs_le_original_q (M n) U
    (finiteCutMasses_ordered us hus j) ⟨T,P,k⟩ (W n) _ H0 H1
  convert H using 1
  ring

end OAI.SKFluctuations.Cavity
