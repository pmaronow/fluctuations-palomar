module

public import ComparisonSignedCavityActualFreshPairEndpointMoment
public import ComparisonSignedCavityActualConstantFreshPairFeedback
public import ComparisonSignedCavityActualInheritedSquareResourceAlong
public import ComparisonSignedCavitySharpEndpointSecondAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

def ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (degree : ℕ) (A gamma sharpSaving Cmass : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→(∀u∈uniformMasses L,u∈us)→
    ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
      let h:=fun l=>((M n).hf (partitionPoint 0 as l):ℝ)
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let C:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
      let q : ℕ→RestCoordinate (dim n)→ℝ:=fun l=>Sum.elim (fun _=>b l) (fun _=>h l)
      ∀(U i k : ℕ) (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [.initial] k T P→1+k ≤ degree→
        i ≤ star→star < U→U ≤ as.length→
      ∀x : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as i ≤ Cmass*x→
      let qfull:=cutFullVariance (dim n) q U 1 1 b h K
      |((W n)⁻¹)^k*nativeActualOriginalFreshPairMoment (dim n) q U b h K C T
        (nativeOriginalCenteredRestTest (dim n) q U b h K T
          (nativeActualResourceRestValue P 0 qfull 0 C)) P.live.test.target star| ≤
        2*|P.coefficient| *A^(1+k)*x*(((dim n+1:ℕ):ℝ)^(-gamma))^k*
          (((dim n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))

theorem actual_fresh_pair_resource_saving_from_genuine_pair_and_sharp_star_along
    {m delta cl cu Az C0 Ct D Bclock gamma sharpSaving Cmass : ℝ}
    (degree : ℕ) (A : ℝ) (hA : 1 ≤ A)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (Hpair : ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A gamma Cmass M W w)
    (Hsharp : ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong sharpSaving M W w) :
    ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong degree A gamma sharpSaving Cmass M W w := by
  filter_upwards [Hpair,Hsharp] with n hnPair hnSharp
  intro L us hus hstar hret hmesh
  filter_upwards [hnPair L us hus hstar hret hmesh,hnSharp us hus hstar] with j hjPair hjSharp
  dsimp only at hjPair hjSharp ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
  let h:=fun l=>((M n).hf (partitionPoint 0 as l):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let C:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun l=>Sum.elim (fun _=>b l) (fun _=>h l)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have Hnode : partitionPoint 0 as star=(w n).star.val:=
    nativeRetainedCut_partitionPoint as ho (w n).star (finiteCutMasses_nodes us j hstar)
  have HCstar : C star=orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    dsimp only [C]
    rw [native_physical_resource_center_at_positive_cut (dim n) (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) as ho star
      (by rw [Hnode];exact (w n).star.property),Hnode]
  intro U i k T P hP hdegree hi hs hU x hxsx hxW hmass
  let qfull:=cutFullVariance (dim n) q U 1 1 b h K
  have HQ : qfull=finitePhysicalCavitySquareVariance (dim n) U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent (dim n) q U 1 b h K
      (finitePhysicalMixedClock (dim n+1) as b h)
  have HM:=hjPair U i k _ (P.retarget 0) hP.retarget hdegree (hi.trans (hs.le.trans hU))
    x hxsx hxW hmass 1 1 (by norm_num) (by norm_num)
  have HMF:=hjPair U i k _ (P.retarget 0).freeze hP.retarget.freeze hdegree
    (hi.trans (hs.le.trans hU)) x hxsx hxW hmass 1 1 (by norm_num) (by norm_num)
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
    (hs.trans_le hU) A x (W n) (((dim n+1:ℕ):ℝ)^(-gamma)) B
    (zero_lt_one.trans_le hA) ((M n).hxs.trans_le hxsx) ((M n).hxs.trans_le (hxs n))
    (by positivity) HB HM HMF HD
  simpa only [List.length_singleton,nativeResourceScale,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,NativeResourceMark.savedScale,mul_one,B] using H

end OAI.SKFluctuations.Cavity
