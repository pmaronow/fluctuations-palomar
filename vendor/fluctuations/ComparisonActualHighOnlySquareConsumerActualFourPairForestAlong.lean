module

public import ComparisonSignedCavityActualFourPairForestAlong
public import ComparisonActualHighOnlySquareConsumerActualFourFreshPairContrastAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum (ActualSlowWindowChoice)
set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

def ActualOriginalFourInitialPairForestSavingAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (k0 depth r : ℕ) (gamma sharpSaving Cmass : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→(∀u∈uniformMasses Lnet,u∈us)→
    ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i : ℕ) (_hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
        (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [.initial] k0 T P→T.leaves ≤ r→
      ∀x : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as i ≤ Cmass*x→
        |nativeActualFourPairSum_high_only (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [⟨T,P,k0⟩])| ≤
          |P.coefficient| *(((dim n+1:ℕ):ℝ)^(-sharpSaving/2))*x*
            ((((dim n+1:ℕ):ℝ)^(-gamma))^(k0+depth))*((M n).xs^2/W n)

theorem actual_inherited_four_initial_pair_forest_saving_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp gamma sharpSaving cK A : ℝ}
    (hTemp : 0 ≤ Temp) (hsharp : 0 < sharpSaving) (hcK : 0 < cK)
    (k0 depth r : ℕ) (hA : 1 ≤ A) (Cmass : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hpair : ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong_high_only
      (1+k0+depth) A gamma sharpSaving Cmass M W w) :
    ActualOriginalFourInitialPairForestSavingAlong_high_only k0 depth r gamma sharpSaving Cmass M W w := by
  let Cweight:=Temp/(Real.exp (-4*Temp)*cK)
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 r depth
  let Cenv:=6*V*A^(1+k0+depth)
  have hV : 0 ≤ V:=nativeActualWeightedFrontierCost_nonneg _ (by dsimp [Cweight];positivity) _ _ _
  have HC:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (native_mass_log_power_decay (q:=sharpSaving) (s:=sharpSaving/2) (by linarith) 0 Cenv)
  filter_upwards [Hpair,htotal,hw,HC] with n hnPair hnTotal hnClock hnC
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hnPair Lnet us hus hstar hret hmesh] with j hjPair
  dsimp only at hjPair ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have hKstar : cK*W n ≤ K star := by
    dsimp only [K,star]
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnClock
  intro U i hi hs hU T P hP hr x hxsx hxW hmass
  let st : NativeActualResourceState (Spin (dim n)×Bool) as i star:=⟨T,P,k0⟩
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let eps:=((dim n+1:ℕ):ℝ)^(-gamma)
  let raw:=3*A^(1+k0+depth)*x*eps^(k0+depth)*(((dim n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have H:=actual_minimum_four_state_forest_abs_le_high_only (M n) hTemp hnTotal hW hcK ho hs hU hKstar
    depth st hr (fun Q=>(W n)⁻¹^Q.generation*nativeActualOriginalFourPairContrast_high_only (M n) U Q)
    (B:=raw) (by dsimp only [raw,eps];positivity) (by
      intro Q hQ
      have HQ:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
        (seed:=[.initial]) (by intro R hR;obtain rfl:=List.mem_singleton.mp hR;exact hP) Q hQ
      have HG:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
        k0 (by intro R hR;obtain rfl:=List.mem_singleton.mp hR;rfl) Q hQ
      have HB:=hjPair U i Q.generation Q.tree Q.term HQ (by omega) hi hs hU x hxsx hxW hmass
      change |(W n)⁻¹^Q.generation*nativeActualOriginalFourPairContrast_high_only (M n) U Q| ≤ _ at HB
      rw [HG] at HB ⊢
      simpa only [raw,eps,Nat.add_assoc,mul_assoc,mul_left_comm,mul_comm] using HB)
  change |nativeActualFourPairSum_high_only (M n) U (W n)
    (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [st])| ≤ _ at H ⊢
  apply H.trans
  have HCn : Cenv*((dim n+1:ℕ):ℝ)^(-sharpSaving) ≤ ((dim n+1:ℕ):ℝ)^(-sharpSaving/2) := by
    simpa only [Function.comp_apply,pow_zero,mul_one,neg_div] using hnC
  have HB:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HCn hx.le)
        (by dsimp only [eps];positivity : 0 ≤ eps^(k0+depth)))
      (by positivity : 0 ≤ (M n).xs^2/W n)) (abs_nonneg P.coefficient)
  convert HB using 1 <;> dsimp only [Cenv,V,Cweight,raw,st,eps] <;> ring

def ActualOriginalConstantFourPairForestSavingAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (k0 depth r : ℕ) (gamma sharpSaving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i : ℕ) (_hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
        (T : ClockTree (Spin (dim n)×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U [] k0 T P→T.leaves ≤ r→
        |nativeActualFourPairSum_high_only (M n) U (W n)
          (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [⟨T,P,k0⟩])| ≤
          |P.coefficient| *(((dim n+1:ℕ):ℝ)^(-sharpSaving/2))*
            ((((dim n+1:ℕ):ℝ)^(-gamma))^(k0+depth))*((M n).xs^2/W n)

theorem actual_inherited_constant_four_pair_forest_saving_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp gamma sharpSaving cK : ℝ}
    (hTemp : 0 ≤ Temp) (hsharp : 0 < sharpSaving) (hcK : 0 < cK)
    (k0 depth r : ℕ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hpair : ActualOriginalConstantFourPairContrastSavingOnEveryFinalNetAlong_high_only
      (k0+depth) gamma sharpSaving M W w) :
    ActualOriginalConstantFourPairForestSavingAlong_high_only k0 depth r gamma sharpSaving M W w := by
  let Cweight:=Temp/(Real.exp (-4*Temp)*cK)
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 r depth
  let Cenv:=6*V
  have hV : 0 ≤ V:=nativeActualWeightedFrontierCost_nonneg _ (by dsimp [Cweight];positivity) _ _ _
  have HC:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (native_mass_log_power_decay (q:=sharpSaving) (s:=sharpSaving/2) (by linarith) 0 Cenv)
  filter_upwards [Hpair,htotal,hw,HC] with n hnPair hnTotal hnClock hnC
  intro us hus hstar
  filter_upwards [hnPair us hus hstar] with j hjPair
  dsimp only at hjPair ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have hKstar : cK*W n ≤ K star := by
    dsimp only [K,star]
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnClock
  intro U i hi hs hU T P hP hr
  let st : NativeActualResourceState (Spin (dim n)×Bool) as i star:=⟨T,P,k0⟩
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let eps:=((dim n+1:ℕ):ℝ)^(-gamma)
  let raw:=3*eps^(k0+depth)*(((dim n+1:ℕ):ℝ)^(-sharpSaving)*((M n).xs^2/W n))
  have H:=actual_minimum_four_state_forest_abs_le_high_only (M n) hTemp hnTotal hW hcK ho hs hU hKstar
    depth st hr (fun Q=>(W n)⁻¹^Q.generation*nativeActualOriginalFourPairContrast_high_only (M n) U Q)
    (B:=raw) (by dsimp only [raw,eps];positivity) (by
      intro Q hQ
      have HQ:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
        (seed:=[]) (by intro R hR;obtain rfl:=List.mem_singleton.mp hR;exact hP) Q hQ
      have HG:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
        k0 (by intro R hR;obtain rfl:=List.mem_singleton.mp hR;rfl) Q hQ
      have HB:=hjPair U i Q.generation Q.tree Q.term HQ (by omega) hi hs hU
      change |(W n)⁻¹^Q.generation*nativeActualOriginalFourPairContrast_high_only (M n) U Q| ≤ _ at HB
      rw [HG] at HB ⊢
      simpa only [raw,eps,Nat.add_assoc,mul_assoc,mul_left_comm,mul_comm] using HB)
  change |nativeActualFourPairSum_high_only (M n) U (W n)
    (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [st])| ≤ _ at H ⊢
  apply H.trans
  have HCn : Cenv*((dim n+1:ℕ):ℝ)^(-sharpSaving) ≤ ((dim n+1:ℕ):ℝ)^(-sharpSaving/2) := by
    simpa only [Function.comp_apply,pow_zero,mul_one,neg_div] using hnC
  have HB:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right HCn
        (by dsimp only [eps];positivity : 0 ≤ eps^(k0+depth)))
      (by positivity : 0 ≤ (M n).xs^2/W n)) (abs_nonneg P.coefficient)
  convert HB using 1 <;> dsimp only [Cenv,V,Cweight,raw,st,eps] <;> ring

end OAI.SKFluctuations.Cavity
