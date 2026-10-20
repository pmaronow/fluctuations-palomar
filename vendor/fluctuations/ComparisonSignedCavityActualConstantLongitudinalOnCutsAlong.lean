module

public import ComparisonSignedCavityActualConstantChildLongitudinalCategoryAlong
public import ComparisonSignedCavityActualConstantSourceClosedRatesAlong
public import ComparisonSignedCavityActualConstantSourceCategoryReduction

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 24000000
variable {dim : ℕ → ℕ}

def ActualConstantSourceLongitudinalOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (C : ℝ)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    ∃hs : star < U,∃hU : U ≤ as.length,
    ∀right : Bool,
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
        (nativeActualConstantSourceChildren (M n) as star U hs hU))
      (nativeActualLongitudinalCategory right)|/(chi*K star) ≤
        C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2

theorem actual_selected_bad_history_constant_longitudinal_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceLongitudinalOnGivenCutsAlong depth C M W w high outer := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_constant_child_longitudinal_category_rate_along
    dim hdim depth Bclock Temp Cf Cmass Cmass cK hTemp hCf hCm hCm hcK
    (D:=D) (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,Hsource,Hps,Htotal,Hcuts,hcompare,HW] with n hn hs hp ht hcuts hcomp hw
  intro L us hus hret hmesh hstar hhigh houter
  have H:=hn (M n) Temp epsilon shell Temp ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    hs hp.2.1 hp.2.2 ht.1 hcomp (by simpa only [hcanonical n] using hw) L us hus hret hmesh
  filter_upwards [H] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,Houter,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  intro right
  have hW : 0 ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos.le
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW)
  have Hhigh':=(partitionPoint_mono _ (finiteCutMasses_ordered us hus j) HUV.le).trans
    (Houter.trans (mul_le_mul_of_nonneg_right hA hW))
  have HH:=hj _ _ Hs (HUV.le.trans HV)
    (by simpa only [hcanonical n] using Hfirst) (by simpa only [hcanonical n] using Hhigh')
    (by simpa only [hcanonical n] using Hmass') (by simpa only [hcanonical n] using HK) right
  simpa only [hcanonical n,nativeActualFourOtherCategorySum] using HH

end OAI.SKFluctuations.Cavity
