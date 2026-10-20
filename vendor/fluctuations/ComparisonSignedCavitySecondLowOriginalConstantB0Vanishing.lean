module

public import ComparisonSignedCavitySecondLowActualOriginalConstantB0Budget
public import ComparisonSignedCavityActualLowErrorSaving

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 30000000

def actualSecondLowOriginalConstantB0Amplitude
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (Temp Cf Couter C : ℝ) : ℝ :=
  16*((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))+
    C*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
      (M.actualOriginalLowErrorDensitySaving (Couter+1)+(1/(n+1:ℕ):ℝ)/M.xs^2)

def ActualSecondLowOriginalConstantB0AmplitudeBoundOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (Couter : ℝ) (eps : ℕ → ℝ)
    (M : (n:ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) star
        ∀(U : ℕ),U ≤ as.length → star < U → partitionPoint 0 as U ≤ Couter*W n →
          |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2| ≤
            eps n*W n*(M n).xs^2

theorem actual_second_low_original_constant_B0_amplitude_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Couter C Ccompare : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare) (hCouter : 0 ≤ Couter)
    (M : (n:ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    Tendsto (fun n=>actualSecondLowOriginalConstantB0Amplitude (M n) Temp Cf Couter C) atTop (𝓝 0) := by
  have HS:=actualOriginalLowErrorDensitySaving_tendsto_zero hm hdelta hroom hcl hcu hAz hC0 hCt
    hCompare M hsmall hWlim hb hh (Couter+1) (by linarith)
  have HI:=actual_low_error_omitted_site_ratio_tendsto_zero hm hC0 M
  have heta:0 < actualMassSavingExponent m delta/32:=div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have HP:=(tendsto_rpow_neg_atTop heta).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have H:=HP.const_mul 16 |>.add ((HS.add HI).const_mul (C*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp))
  simpa only [actualSecondLowOriginalConstantB0Amplitude,Function.comp_def,add_zero,mul_zero] using H

theorem actual_second_low_original_constant_B0_vanishing
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Cf Ccompare : ℝ}
    (Couter : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCouter : 0 ≤ Couter) (hCompare : 0 ≤ Ccompare)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n:ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    ∃eps : ℕ → ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualSecondLowOriginalConstantB0AmplitudeBoundOnEveryFinalNet Couter eps M W w := by
  obtain ⟨C,hC,HB⟩:=actual_second_low_original_constant_B0_budget Couter hTemp hCf hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt M W hcanonical hWlim w Hsource hw
  let eps:=fun n=>actualSecondLowOriginalConstantB0Amplitude (M n) Temp Cf Couter C
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE]
    exact hWlim
  refine ⟨eps,?_,actual_second_low_original_constant_B0_amplitude_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hCouter M hsmall HL hb hh,?_⟩
  · intro n
    have HS:0 < (M n).actualOriginalLowErrorDensitySaving (Couter+1):=
      (M n).actualOriginalLowErrorDensitySaving_pos (by linarith)
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    dsimp [eps,actualSecondLowOriginalConstantB0Amplitude]
    positivity
  · filter_upwards [HB] with n hn
    intro L us hus hstar hret hmesh
    filter_upwards [hn L us hus hstar hret hmesh] with jGrid hgrid
    dsimp only at hgrid ⊢
    intro U hU hstarU houter
    have H:=hgrid U hU hstarU houter
    let as:=finiteCutMasses us jGrid
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hx:0 < (M n).xs:=(M n).hxs
    have hW:0 ≤ W n:=hx.le.trans ((M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm)
    have HCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    have Hrho:(M n).actualOriginalLowErrorDensitySaving (Couter+1)*(M n).xs^2+
        partitionPoint 0 as U/(n+1:ℕ) ≤
        ((M n).actualOriginalLowErrorDensitySaving (Couter+1)+(1/(n+1:ℕ):ℝ)/(M n).xs^2)*(M n).xs^2:=by
      rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (partitionPoint_mem as ho U).2 (by positivity))
    apply H.trans
    have HH:=add_le_add_left (mul_le_mul_of_nonneg_left Hrho (mul_nonneg (mul_nonneg hC.le hW) HCerr))
      (16*((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2)
    convert HH using 1 <;> (try dsimp [eps,actualSecondLowOriginalConstantB0Amplitude]) <;> ring

end OAI.SKFluctuations.Cavity
