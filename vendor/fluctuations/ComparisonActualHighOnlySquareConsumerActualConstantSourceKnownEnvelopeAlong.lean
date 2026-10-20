module

public import ComparisonSignedCavityActualConstantSourceKnownEnvelopeAlong
public import ComparisonActualHighOnlySquareConsumerActualConstantSourceChildrenFrozenAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum (ActualSlowWindowChoice)
set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

def nativeActualConstantSourceKnownEnvelope_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {star U : ℕ} (hs : star<U) (hU : U≤ as.length)
    (W Temp cK gamma sharpSaving terminalSaving : ℝ) (depth : ℕ) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let bstar:=(M.bf (partitionPoint 0 as star):ℝ)
  let N:=((n+1:ℕ):ℝ)
  let eps:=N^(-gamma)
  let children:=nativeActualConstantSourceChildren_high_only M as star U hs hU
  bstar*W*(
    ((List.range depth).map (fun j=>
      (|1-bstar*chi^2| *(6*(N^(-sharpSaving/2)*eps^(1+j)*(M.xs^2/W)))+
        |nativeActualFourOtherSourceErrorSum_high_only M U W
          (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|)/
        (Real.exp (-4*Temp)*cK*W)+
      6*(N^(-(1:ℝ)/6)*M.xs^2*eps^(1+j+1))+
      |nativeActualFourFirstHighErrorSum_high_only M U W
        (nativeActualMinimumFourCenteredForest_high_only M hs hU W j children)|)).sum+
    12*(N^(-terminalSaving)*M.xs^2)+N^(-(1:ℝ)/6)*M.xs^2*eps)+
  |nativeActualConstantSourceRemainder_high_only M as star U|

def ActualConstantSourceKnownEnvelopeAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (Temp cK gamma sharpSaving terminalSaving : ℝ)
    (depth : ℕ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U : ℕ) (hs : star<U) (hU : U≤ as.length),
        |nativeActualMinimumConstantJointSource_high_only (M n) as star U|≤
          nativeActualConstantSourceKnownEnvelope_high_only (M n) hs hU (W n)
            Temp cK gamma sharpSaving terminalSaving depth

theorem actual_constant_source_known_envelope_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp cK gamma sharpSaving terminalSaving : ℝ}
    (hcK : 0<cK) (depth : ℕ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,cK*W n≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hpair : ∀j : ℕ,j<depth→ActualOriginalConstantSourceChildrenPairLevelSavingAlong_high_only j gamma sharpSaving M W w)
    (Hfrozen : ∀j : ℕ,j<depth→ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong_high_only j gamma M W w)
    (Hinitial : ActualOriginalConstantSourceChildrenFrozenSavingAlong_high_only gamma M W w)
    (Hterm : ActualOriginalConstantSourceChildrenFourTerminalSavingAlong_high_only depth terminalSaving M W w) :
    ActualConstantSourceKnownEnvelopeAlong_high_only Temp cK gamma sharpSaving terminalSaving depth M W w := by
  have HP:=Filter.eventually_all.mpr (fun j : Fin depth=>Hpair j.val j.isLt)
  have HF:=Filter.eventually_all.mpr (fun j : Fin depth=>Hfrozen j.val j.isLt)
  filter_upwards [HP,HF,Hinitial,Hterm,htotal,hw] with n hnP hnF hnI hnT hnTotal hnClock
  intro us hus hstar
  have HPgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnP d us hus hstar)
  have HFgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnF d us hus hstar)
  filter_upwards [HPgrid,HFgrid,hnI us hus hstar,hnT us hus hstar] with j hjP hjF hjI hjT
  dsimp only at hjP hjF hjI hjT ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0<W n:=(M n).hxs.trans_le (hxs n)
  have HK : cK*W n≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star:=by
    dsimp only [star]
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnClock
  intro U hs hU
  let N:=((dim n+1:ℕ):ℝ)
  let eps:=N^(-gamma)
  let bstar:=((M n).bf (partitionPoint 0 as star):ℝ)
  let children:=nativeActualConstantSourceChildren_high_only (M n) as star U hs hU
  let Bpair:=fun d=>6*(N^(-sharpSaving/2)*eps^(1+d)*((M n).xs^2/W n))
  let Bfrozen:=fun d=>6*(N^(-(1:ℝ)/6)*(M n).xs^2*eps^(1+d+1))
  let Bother:=fun d=>|nativeActualFourOtherSourceErrorSum_high_only (M n) U (W n)
    (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) d children)|
  let Bfirst:=fun d=>|nativeActualFourFirstHighErrorSum_high_only (M n) U (W n)
    (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) d children)|
  have H:=actual_minimum_constant_joint_source_abs_le_of_four_budgets_high_only (M n) hnTotal
    hW hcK ho hs hU HK depth Bpair Bother Bfirst Bfrozen
    (fun d hd=>hjP ⟨d,hd⟩ U hs hU) (fun _ _=>le_rfl) (fun _ _=>le_rfl)
    (fun d hd=>hjF ⟨d,hd⟩ U hs hU) (hjT U hs hU)
  have HI:=hjI U hs hU
  have HB : 0≤ bstar*W n:=mul_nonneg (NNReal.coe_nonneg _) hW.le
  have Hcorr : |nativeActualConstantSourceFrozenCorrection_high_only (M n) as star U hs hU (W n)|≤
      |nativeActualConstantSourceRemainder_high_only (M n) as star U|+
        bstar*W n*(N^(-(1:ℝ)/6)*(M n).xs^2*eps):=by
    unfold nativeActualConstantSourceFrozenCorrection_high_only
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg HB]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left HI HB)
  apply H.trans
  apply (add_le_add le_rfl Hcorr).trans_eq
  dsimp only [nativeActualConstantSourceKnownEnvelope_high_only,Bpair,Bfrozen,Bother,Bfirst,
    children,bstar,eps,N]
  ring

end OAI.SKFluctuations.Cavity
