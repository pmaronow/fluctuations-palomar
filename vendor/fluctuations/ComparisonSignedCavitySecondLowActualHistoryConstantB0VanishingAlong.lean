module

public import ComparisonSignedCavitySecondLowInheritedConstantB0AmplitudeAlong
public import ComparisonSignedCavitySecondLowActualOriginalConstantB0BudgetAlong
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 30000000

def ActualSecondLowOriginalConstantB0AmplitudeBoundOnEveryFinalNetAlong
    {dim : ℕ → ℕ}
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (Couter : ℝ) (eps : ℕ → ℝ)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) : Prop :=
    ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us →
      (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ → RestCoordinate (dim n) → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) star
        ∀(U : ℕ),U ≤ as.length → star < U → partitionPoint 0 as U ≤ Couter*W n →
          |nativeSecondLowJointLedger (dim n) q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2| ≤
            eps n*W n*(M n).xs^2

theorem actual_second_low_actual_history_constant_B0_vanishing_along
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs Ccompare c0 : ℝ}
    (Couter : ℝ) (hTemp : 0 ≤ Temp) (hCouter : 0 ≤ Couter) (hCompare : 0 ≤ Ccompare)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃eps : ℕ → ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualSecondLowOriginalConstantB0AmplitudeBoundOnEveryFinalNetAlong Couter eps M W w := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨C,hC,HB⟩:=actual_second_low_original_constant_B0_budget_along Couter hTemp hCf hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim w Hsource hw
  let eps:=fun n=>actualSecondLowOriginalConstantB0Amplitude (M n) Temp Cf Couter C
  have HL:Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE:(fun n=>(M n).canonicalDirectTestBandScale)=W:=by funext n;exact (hcanonical n).symm
    rw [HE]
    exact hWlim
  refine ⟨eps,?_,actual_second_low_inherited_constant_B0_amplitude_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hCompare hCouter dim hdim root M epsilon shell
    hb hh Hhistory hsmall HL,?_⟩
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
        partitionPoint 0 as U/(dim n+1:ℕ) ≤
        ((M n).actualOriginalLowErrorDensitySaving (Couter+1)+(1/(dim n+1:ℕ):ℝ)/(M n).xs^2)*(M n).xs^2:=by
      rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (partitionPoint_mem as ho U).2 (by positivity))
    apply H.trans
    have HH:=add_le_add_left (mul_le_mul_of_nonneg_left Hrho (mul_nonneg (mul_nonneg hC.le hW) HCerr))
      (16*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*W n*(M n).xs^2)
    convert HH using 1 <;> (try dsimp [eps,actualSecondLowOriginalConstantB0Amplitude]) <;> ring

end OAI.SKFluctuations.Cavity
