module

public import ComparisonSignedCavitySecondLowActualConstantChildStarOnlyB0CategoryAlong
public import ComparisonSignedCavityActualStrongSharpSourceCutReadout
public import ComparisonSignedCavityActualConstantB0CategoryEnvelope
public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

theorem actual_constant_second_low_family_reindex
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as mid tail : List PositiveMass) (hparts : as=mid++tail)
    (star U : ℕ) (hindex : mid.length=star) (hs : star<U) (hU : U≤as.length)
    (hs' : mid.length<U) (hU' : U≤(mid++tail).length) (W B : ℝ) (depth : ℕ)
    (H :
      let K:=nativeContinuumMixedClock n M.bf M.hf (mid++tail)
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks (mid++tail) (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs' hU' W depth
          (nativeActualConstantSourceChildren M (mid++tail) mid.length U hs' hU')) .secondLow|/
        (chi*K mid.length) ≤ B) :
      let K:=nativeContinuumMixedClock n M.bf M.hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W depth
          (nativeActualConstantSourceChildren M as star U hs hU)) .secondLow|/(chi*K star) ≤ B := by
  subst as
  subst star
  exact H

def ActualConstantB0OnStrongGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star<U,∃hU : U ≤ as.length,
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) .secondLow|/(chi*K star) ≤
            err n*(M n).xs^2

theorem actual_inherited_constant_b0_on_strong_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK A Rmacro Cx : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hmacro : 0<Rmacro) (hRhalf : Rmacro≤1/2) (hCx : 0<Cx)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A Rmacro Cx) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualConstantB0OnStrongGivenCutsAlong depth err M W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  have Hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1:=by
    filter_upwards [Hshell] with n hn
    rcases hn with ⟨Tbase,epsilon,shell,ts,hb,hh⟩
    exact NativePullbackClockRegularity.of_shell_history
      (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
      (M n).alpha Tbase epsilon shell ts (M n).b (M n).h hb hh le_rfl zero_le_one le_rfl
  let F:=max (1+2*cu) (1+1/Rmacro)
  obtain ⟨eps,heps,hE,HE⟩:=actual_inherited_constant_resource_star_only_full_B0_saving_along
    (eta:=m) (1+depth) (3+6*depth+1) A A Ccal Rmacro F Cx hCx hm hTemp hCf hA0.le hA0.le hCcal
    hm hdelta hroom (by linarith) hcl hcu hAz hC0 hCt hmacro hRhalf (le_max_left _ _) (le_max_right _ _)
    dim hdim M W hcanonical hWlim w Hsource Hclock hcompare hw
  have HH:=actual_constant_resource_star_only_full_half_B0_from_resource_rows_along
    (1+depth) (3+6*depth) A A Rmacro Cx eps dim M W w HE
  obtain ⟨e,he,HF⟩:=actual_constant_child_star_only_full_B0_from_actual_half_rows_along
    depth Bclock Temp Cf A A Rmacro Cx cK hTemp hCf hcK dim M W hcanonical hWlim Hsource w
    (fun n=>(3/2:ℝ)*eps n) (fun n=>mul_nonneg (by norm_num) (heps n))
    (by simpa only [mul_zero] using hE.const_mul (3/2:ℝ)) HH
  refine ⟨fun n=>|e n|,(fun n=>abs_nonneg _),by simpa only [abs_zero] using he.abs,?_⟩
  filter_upwards [HF,Hcuts] with n hn hcuts
  intro L us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hn L us hus hstar hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨hs,HUV,HV,_,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.toActualSharpSourceCutGeometry.finite_net_readout us hus hstar hhigh houter jGrid
  obtain ⟨_,_,_,_,Hhighmass,_,Hfour,HstarR,Hz,HCx,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hupper:partitionPoint 0 as U≤A*W n:=(partitionPoint_mono as ho HUV.le).trans Houter
  let mid:=as.take star
  let tail:=as.drop star
  have hparts:as=mid++tail:=(List.take_append_drop star as).symm
  have hindex:mid.length=star:=List.length_take_of_le (retainedMassPrefixIndex_le_length _ _)
  have hs':mid.length<U:=by simpa only [hindex] using hs
  have hU':U≤(mid++tail).length:=by rw [←hparts];exact hU
  have H:=hj mid tail hparts hindex U hs' hU' Hupper
    (by simpa only [hindex] using Hmass) Hfour Hz (by simpa only [hindex] using HstarR)
    (high n).val (high n).property (by simpa only [Hhighmass] using HCx) Hhighmass hnodes
    (by simpa only [hindex] using HstarK)
  refine ⟨hs,hU,?_⟩
  have H':=H.trans (mul_le_mul_of_nonneg_right (le_abs_self (e n)) (sq_nonneg _))
  exact actual_constant_second_low_family_reindex (M n) as mid tail hparts star U hindex
    hs hU hs' hU' (W n) (|e n| *(M n).xs^2) depth H'

end OAI.SKFluctuations.Cavity
