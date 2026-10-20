module

public import ComparisonSignedCavityActualConstantB0CategoryEnvelope
public import ComparisonSignedCavityActualConstantChildGammaLowRateAlong
public import ComparisonSignedCavityActualConstantChildGammaHighCategoryAlong
public import ComparisonSignedCavityActualConstantLongitudinalOnCutsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantGammaRestorationOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star<U,∃hU : U ≤ as.length,
      ∀cat∈nativeActualSavedGammaRestorationCategories,
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) cat|/(chi*K star) ≤
            err n*(M n).xs^2

theorem actual_inherited_constant_gamma_restoration_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar Lwin Cwindow c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
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
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualConstantGammaRestorationOnGivenCutsAlong depth err M W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨eL,heL,HL⟩:=actual_inherited_constant_child_gamma_LOW_restoration_category_rate_along
    depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource w hw
  obtain ⟨eH,heH,HH⟩:=actual_inherited_constant_child_gamma_HIGH_restoration_category_rate_along
    depth Bclock Temp Cf A Ccal cK hTemp hCf hA0.le hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource hcompare Hshell w
  let err n:=|eL n|+|eH n|
  have herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,abs_zero,zero_add] using heL.abs.add heH.abs
  refine ⟨err,(fun n=>by dsimp only [err];positivity),herr,?_⟩
  filter_upwards [HL,HH,Hcuts] with n hnL hnH hcuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hnL L us hus hret hmesh hstar,hnH L us hus hret hmesh hstar] with jGrid hjL hjH
  dsimp only at hjL hjH ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ min (A*W n) 1:=
    le_min ((partitionPoint_mono as ho HUV.le).trans Houter) (partitionPoint_mem as ho U).2
  have HL':=hjL U hs hU Hupper Hmass HstarK
  have HH':=hjH U hs hU Hlo Hmass HstarK
  refine ⟨hs,hU,?_⟩
  intro cat hcat
  simp only [nativeActualSavedGammaRestorationCategories,List.mem_cons,List.not_mem_nil,or_false] at hcat
  have hle : eL n ≤ err n:=by
    dsimp only [err]
    linarith [le_abs_self (eL n),abs_nonneg (eH n)]
  have hhe : eH n ≤ err n:=by
    dsimp only [err]
    linarith [le_abs_self (eH n),abs_nonneg (eL n)]
  rcases hcat with rfl|rfl
  · exact HH'.trans (mul_le_mul_of_nonneg_right hhe (sq_nonneg _))
  · exact HL'.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _))

end OAI.SKFluctuations.Cavity
