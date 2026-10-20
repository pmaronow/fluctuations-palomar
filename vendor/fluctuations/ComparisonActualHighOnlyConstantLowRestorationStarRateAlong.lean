module

public import ComparisonActualHighOnlyLowRestorationCompatibleSourceAlong
public import ComparisonActualHighOnlyOriginalTargetB0
public import ComparisonActualHighOnlyOriginalTaylorProfiles
public import ComparisonActualHighOnlySquareConsumerActualSharpFourTerminalAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization NativeOverlapMinimum

theorem actual_inherited_constant_low_restoration_star_rate_along_high_only
    (rBound : ℕ)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s≤1/4 ∧ (M n).data.s≤(M n).xs)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar Lwin Cs (w n)) :
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→(w n).star∈us→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        partitionPoint 0 as U ≤ Ccut*W n→
        ∀a z : T.Slot,T.splitIndex a z=star→star < U→
          |nativeCenteredLowGammaLowRestoration (dim n) q U b h K S T
            (fun _=>1) a z|≤
            ((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(W n*(M n).xs^2) := by
  obtain ⟨Cq,hCq,HP⟩:=eventually_actual_minimum_inherited_constant_low_restoration_ledger_high_only
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mc:=4*Cf+2*Temp
  let A:=4*(rBound:ℝ)*(rBound+1)*ClockTree.absJetVariation (rBound+2) 2*
    actualLowErrorComparisonConstant Mc Temp*(Cq*(1+Ccut))^2
  have hA : 0 ≤ A := by
    dsimp only [A]
    have H:=ClockTree.absJetVariation_nonneg (rBound+2) 2
    have Hc:=actualLowErrorComparisonConstant_nonneg Mc hTemp
    positivity
  have HR:=eventually_actual_sharp_star_original_low_radius_saving_along_high_only hm hdelta hC0 A hA dim hdim M W hcanonical hWlim w hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hdim.eventually HP,HR,HW1,hsource,Hcutoff] with n hnP hnR hnW hnSource hnCutoff
  have hxsW : (M n).xs ≤ W n:=by rw [hcanonical];exact le_max_left _ _
  intro L us hus hret hmesh hstar
  filter_upwards [hnP (M n) hnCutoff.1 hnCutoff.2 hnSource (hxsW.trans hnW) L us hus hret hmesh,
    hnR us hus hstar] with jGrid hgrid hrad
  dsimp only at hgrid hrad ⊢
  intro U T hU hT hcut a z hsplit hlow
  have HE:=hgrid U T hU hT (W n) hxsW hcut a z (hsplit.trans_lt hlow)
  rw [hsplit] at HE
  have hW : 0 < W n:=(M n).hxs.trans_le hxsW
  have HH:=mul_le_mul_of_nonneg_right hrad (show 0 ≤ (W n)^2 by positivity)
  apply HE.trans
  convert HH using 1
  · dsimp only [A,Mc]
    ring
  · field_simp

end OAI.SKFluctuations.Cavity
