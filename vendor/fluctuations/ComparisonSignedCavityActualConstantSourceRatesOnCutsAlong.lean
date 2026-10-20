module

public import ComparisonSignedCavityActualConstantSourceFirstHighRate
public import ComparisonSignedCavityActualConstantSourceGaCurrentAlong
public import ComparisonSignedCavityActualSharpSourceCutReadout
public import ComparisonNativeActualHistoryScalarEndpointLimits
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 26000000
variable {dim : ℕ → ℕ}

def ActualConstantSourceGaCurrentOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta C : ℝ)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    ∃hs : star < U,∃hU : U ≤ as.length,
    ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError (M n) U (W n) Q|)).sum ≤
      C*(dim n:ℝ)^(-eta)*(M n).xs^2

def ActualConstantSourceFirstHighOnGivenCutsAlong
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
    ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U (W n) Q|)).sum ≤
      C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2

theorem ActualConstantSourceGaCurrentOnEveryFinalNetAlong.on_given_cuts
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C cFirst A : ℝ} {depth : ℕ}
    {M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius : ℕ → ℝ} {w : ℕ → ActualSlowWindowChoice} {high outer : ℕ → PositiveMass}
    (H : ActualConstantSourceGaCurrentOnEveryFinalNetAlong depth eta Cmass cK C M W w)
    (hxs : ∀n,(M n).xs ≤ W n) (hA : A ≤ Cmass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ActualConstantSourceGaCurrentOnGivenCutsAlong depth eta C M W w high outer := by
  filter_upwards [H,Hcuts] with n hn hnCuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,Hrad,Hrad1,HRU,HRstar,Hrz,HK,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  exact hj _ Hs (HUV.le.trans HV) (radius n)
    (Hmass.trans (mul_le_mul_of_nonneg_right hA ((M n).hxs.trans_le (hxs n)).le))
    Hrad Hrad1 HRU HRstar Hrz HK

theorem actual_selected_bad_history_constant_source_first_high_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
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
    ∃C : ℝ,0 < C ∧ ActualConstantSourceFirstHighOnGivenCutsAlong depth C M W w high outer := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_constant_source_first_high_rate
    (D:=D) depth Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu) cK
    hTemp hCf hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*W n ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,Hps,Htotal,Hcuts,hcompare,HW,HG]
    with n hn hs hp ht hcuts hcomp hw hg
  intro L us hus hret hmesh hstar hhigh houter
  have H:=hn (M n) Temp epsilon shell Temp ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    hp.2.1 hp.2.2 hs ht.1 hcomp
    (by norm_num;simpa only [hcanonical n] using hw) (by norm_num;simpa only [hcanonical n,one_div] using hg)
    L us hus hret hmesh
  filter_upwards [H] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  have hW : 0 ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos.le
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW)
  have HH:=hj _ _ Hs (HUV.le.trans HV)
    (by simpa only [hcanonical n] using Hfirst)
    (by simpa only [hcanonical n] using Hmass') (by simpa only [hcanonical n] using HK)
  simpa only [hcanonical n] using HH

theorem actual_selected_bad_history_constant_source_rates_on_given_cuts_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (heta : 0 < eta) (hgap : 2*eta < 6*m)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ → ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃Cg Cf : ℝ,0 < Cg ∧ 0 < Cf ∧
      ActualConstantSourceGaCurrentOnGivenCutsAlong depth eta Cg M W w high outer ∧
      ActualConstantSourceFirstHighOnGivenCutsAlong depth Cf M W w high outer := by
  obtain ⟨Cfield,hCfield,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨Cg,hCg,HG⟩:=eventually_inherited_same_star_constant_source_Ga_current_along hdim
    depth Cmass cK hCm hcK heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hTemp hCfield hCcal M W hcanonical hWlim hcompare Hsource
    (Htotal.mono (fun _ h=>h.1)) saving hsaving w Hmixed
  obtain ⟨Cf,hCf,HF⟩:=actual_selected_bad_history_constant_source_first_high_on_given_cuts_along
    depth Cmass (zero_le_one.trans hCm) hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCcal hc0 hmargin hcapmargin hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
    W radius hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  exact ⟨Cg,Cf,hCg,hCf,HG.on_given_cuts
    (fun n=>(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm) hA Hcuts,HF⟩

end OAI.SKFluctuations.Cavity
