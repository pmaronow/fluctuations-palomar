module

public import ComparisonSignedCavityActualRetainedGammaCategorySum
public import ComparisonSignedCavityActualInitialGammaLowRateAlong
public import ComparisonSignedCavityActualInitialGammaHighCategoryAlong
public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def nativeActualThreeGammaCategoryEnvelope
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  |nativeActualFourOtherCategorySum M U W rows .gammaRetained|/(chi*K star)+
    |nativeActualFourOtherCategorySum M U W rows .gammaHighRestoration|/(chi*K star)+
    |nativeActualFourOtherCategorySum M U W rows .gammaLowRestoration|/(chi*K star)

def ActualInitialThreeGammaOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*x n →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        nativeActualThreeGammaCategoryEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
            [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length)
              seedMass (by omega)]) ≤ err n*(x n*(M n).xs^2)

theorem actual_inherited_initial_three_Gamma_on_given_cuts_along
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
    (x : ℕ→ℝ) (hxsx : ∀ᶠn in atTop,(M n).xs ≤ x n) (hxW : ∀ᶠn in atTop,x n ≤ W n)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (saving : ℝ) (hsaving : 0 ≤ saving)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialThreeGammaOnGivenCutsAlong depth A err M x W w high outer := by
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  obtain ⟨C,hC,HG⟩:=eventually_inherited_same_star_four_retained_Gamma_initial_along
    (eta:=m) hdim depth A cK hA hcK hm hm hdelta hroom (by linarith)
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare Hsource saving hsaving w Hmixed
  obtain ⟨eL,heL,HL⟩:=actual_inherited_initial_gamma_LOW_restoration_category_rate_along
    depth Bclock Temp Cf A A cK hTemp hCf hA0.le hA0 hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hcanonical hWlim Hsource x hxsx hxW w hw
  obtain ⟨eH,heH,HH⟩:=actual_inherited_initial_gamma_HIGH_restoration_category_rate_along
    depth Bclock Temp Cf A Ccal cK hTemp hCf hA0.le hCcal hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcouter
    dim hdim M W hcanonical hWlim Hsource x hxsx hxW hcompare Hshell w
  let eG n:=C*(dim n:ℝ)^(-m)
  let err n:=eG n+|eH n|+|eL n|
  have hG n : 0 ≤ eG n:=by dsimp only [eG];positivity
  have heG : Tendsto eG atTop (𝓝 0):=by
    simpa only [eG,Function.comp_def,mul_zero] using
      ((tendsto_rpow_neg_atTop hm).comp (tendsto_natCast_atTop_atTop.comp hdim)).const_mul C
  have herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,abs_zero,zero_add] using (heG.add heH.abs).add heL.abs
  refine ⟨err,(fun n=>by dsimp only [err];positivity),herr,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HG,HL,HH,Hcuts,Hsource,HW,hxsx,hxW] with n hnG hnL hnH hcuts hsClocks hW1 hnx hnW
  have hxWn : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxWn
  have hx : 0 < x n:=(M n).hxs.trans_le hnx
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hnG L us hus hret hmesh hstar,hnL L us hus hret hmesh hstar,
    hnH L us hus hret hmesh hstar] with jGrid hjG hjL hjH
  dsimp only at hjG hjL hjH ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,Hrad,Hrad1,HradU,HstarR,Hz,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ min (A*W n) 1:=
    le_min ((partitionPoint_mono as ho HUV.le).trans Houter) (partitionPoint_mem as ho U).2
  intro pre mid tail hcut hindex hmid hmi
  have HI : pre.length+mid.length<U:=by rw [hindex];exact hs
  have HU : U ≤ (pre++(mid++tail)).length:=by rw [hcut];exact hU
  have hindex' : retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))=pre.length+mid.length:=by
    rw [hcut];exact hindex.symm
  have ho' : MassOrdered 0 (pre++(mid++tail)):=by rw [hcut];exact ho
  have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf
      (pre++(mid++tail)) (pre.length+mid.length):=by rw [hcut,hindex];exact HstarK
  rw [←hcut] at hjL hjH
  let PR (cat : NativeActualOtherSourceCategory) (e : ℝ) (ss : ℕ) : Prop:=
    ∀(hi : pre.length ≤ ss) (hs' : ss<U) (seedMass : ℝ),
      |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs' HU (W n) depth
          [nativeActualInitialState (pre++(mid++tail)) pre.length ss seedMass
            (hi.trans (hs'.le.trans HU))]) cat|/
        ((scalarTerminal.schedule (scalarBoundaryClocks (pre++(mid++tail))
          (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)))))).H 0 0*
          nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)) ss) ≤
        e*(x n*(M n).xs^2)
  have HL0 : PR .gammaLowRestoration (eL n) (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))):=by
    intro hi hs' seedMass
    exact hjL pre.length U hi hs' HU (by simpa only [hcut] using Hupper)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using Hmass)
      (by simpa only [hcut] using HstarK) seedMass
  have HH0 : PR .gammaHighRestoration (eH n) (retainedMassPrefixIndex (w n).star.val (pre++(mid++tail))):=by
    intro hi hs' seedMass
    exact hjH pre.length U hi hs' HU (by simpa only [hcut] using Hlo)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using Hmass)
      (by simpa only [hcut] using HstarK) seedMass
  have HL : PR .gammaLowRestoration (eL n) (pre.length+mid.length):=hindex' ▸ HL0
  have HH : PR .gammaHighRestoration (eH n) (pre.length+mid.length):=hindex' ▸ HH0
  refine ⟨HI,HU,?_⟩
  intro seedMass
  have HG:=hjG pre mid tail hcut hindex (by rw [hindex];exact Hmass) hmid U HI HU
    seedMass (x n) (radius n) hnx hnW hmi Hrad Hrad1 HradU
    (by rw [hindex];exact HstarR) Hz (by rw [hindex];exact HstarK)
  have Hbound:=(actual_retained_gamma_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks
    (hxWn.trans hW1) ho' HI HU hW hcK HK _).trans HG
  have HG' : |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) seedMass (by omega)])
      .gammaRetained|/((scalarTerminal.schedule (scalarBoundaryClocks (pre++(mid++tail))
        (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)))))).H 0 0*
          nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (pre++(mid++tail)) (pre.length+mid.length)) ≤
        eG n*(x n*(M n).xs^2):=by
    apply Hbound.trans_eq
    dsimp only [eG]
    ring
  have HL':=HL (by omega) HI seedMass
  have HH':=HH (by omega) HI seedMass
  have Hsum:=add_le_add (add_le_add HG' HH') HL'
  change nativeActualThreeGammaCategoryEnvelope (M n) U (W n) _ ≤ _
  apply Hsum.trans
  have HHL:=add_le_add (le_abs_self (eH n)) (le_abs_self (eL n))
  have HE:=mul_le_mul_of_nonneg_right (add_le_add_left HHL (eG n))
    (show 0 ≤ x n*(M n).xs^2 by positivity)
  convert HE using 1 <;> (try dsimp only [err]) <;> ring

end OAI.SKFluctuations.Cavity
