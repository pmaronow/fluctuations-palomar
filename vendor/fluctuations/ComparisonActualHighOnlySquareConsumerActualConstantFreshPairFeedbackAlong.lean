module

public import ComparisonSignedCavityActualConstantFreshPairFeedbackAlong
public import ComparisonActualHighOnlySquareConsumerActualFreshPairEndpointMomentAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum (ActualSlowWindowChoice)
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

def ActualOriginalConstantFreshPairSavingOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree : ℕ) (gamma sharpSaving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
      let h:=fun l=>((M n).hf (partitionPoint 0 as l):ℝ)
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let C:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
      let q : ℕ→RestCoordinate (dim n)→ℝ:=fun l=>Sum.elim (fun _=>b l) (fun _=>h l)
      ∀(U i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [] k T P→k ≤ degree→
        i ≤ star→star < U→U ≤ as.length→
      let qfull:=cutFullVariance (dim n) q U 1 1 b h K
      |((W n)⁻¹)^k*nativeActualOriginalFreshPairMoment (dim n) q U b h K C T
        (nativeOriginalCenteredRestTest (dim n) q U b h K T
          (nativeActualResourceRestValue P 0 qfull 0 C)) P.live.test.target star| ≤
        2*|P.coefficient| *(((dim n+1:ℕ):ℝ)^(-gamma))^k*
          (((dim n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))

theorem actual_constant_fresh_pair_saving_from_genuine_pair_and_sharp_star_along_high_only
    {m delta cl cu Az C0 Ct D Bclock gamma sharpSaving : ℝ}
    (degree : ℕ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (Hpair : ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong_high_only degree 1 gamma M W w)
    (Hsharp : ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong_high_only sharpSaving M W w) :
    ActualOriginalConstantFreshPairSavingOnEveryFinalNetAlong_high_only degree gamma sharpSaving M W w := by
  filter_upwards [Hpair,Hsharp] with n hnPair hnSharp
  intro us hus hstar
  filter_upwards [hnPair us hus hstar,hnSharp us hus hstar] with j hjPair hjSharp
  dsimp only at hjPair hjSharp ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
  let h:=fun l=>((M n).hf (partitionPoint 0 as l):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let C:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun l=>Sum.elim (fun _=>b l) (fun _=>h l)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have Hnode : partitionPoint 0 as star=(w n).star.val:=
    nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us j hstar)
  have HCstar : C star=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    dsimp only [C]
    rw [native_physical_resource_center_at_positive_cut (dim n) (M n).bf (M n).hf
      ((M n).bf_monotone) ((M n).hf_monotone) as ho star
      (by rw [Hnode];exact (w n).star.property),Hnode]
  intro U i k T P hP hdegree hi hs hU
  let qfull:=cutFullVariance (dim n) q U 1 1 b h K
  have HQ : qfull=finitePhysicalCavitySquareVariance (dim n) U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent (dim n) q U 1 b h K
      (finitePhysicalMixedClock (dim n+1) as b h)
  have HM:=hjPair U i k _ (P.retarget 0) hP.retarget hdegree (M n).xs 1 1 (by norm_num) (by norm_num)
  have HMF:=hjPair U i k _ (P.retarget 0).freeze hP.retarget.freeze hdegree (M n).xs 1 1 (by norm_num) (by norm_num)
  rw [←HQ] at HM HMF
  let B:=((dim n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n)
  have hWn : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have HB : 0 ≤ B:=by dsimp only [B];positivity
  have HD : (nativeFreshAtSlot T 0 P.live.test.target star).tree.disorderExpect
      (fullWeight (dim n)) (fullFeature (dim n)) 0 qfull
      (fun σ=>(deletedOverlap (dim n)
        (joinSpin (T.atSlot ((nativeFreshAtSlot T 0 P.live.test.target star).restrict σ) P.live.test.target))
        (joinSpin ((nativeFreshAtSlot T 0 P.live.test.target star).spin σ))-C star)^2) 0 ≤ B^2 := by
    rw [native_actual_fresh_star_endpoint_second_eq_pair (dim n) T ho _ star U (hs.le.trans hU),HCstar]
    exact hjSharp U
  have H:=normalized_actual_centered_fresh_pair_moment_abs_le q b h K C T P hP ho hi
    (hs.trans_le hU) 1 (M n).xs (W n) (((dim n+1:ℕ):ℝ)^(-gamma)) B
    (by norm_num) (M n).hxs ((M n).hxs.trans_le (hxs n))
    (by positivity) HB HM HMF HD
  simpa only [List.length_nil,nativeResourceScale,List.map_nil,List.prod_nil,
    pow_zero,one_pow,mul_one,B] using H

end OAI.SKFluctuations.Cavity
