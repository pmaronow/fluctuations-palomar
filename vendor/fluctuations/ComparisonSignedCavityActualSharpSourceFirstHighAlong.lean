module

public import ComparisonSignedCavityActualSharpSourceCurrentGaAlong
public import ComparisonSignedCavityActualHistoryFourFirstHighAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

def ActualSharpSourceFirstHighInitialOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Cmass C : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let U:=retainedMassPrefixIndex (high n).val as
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∃hs : pre.length+mid.length<U,∃hU : U≤(pre++(mid++tail)).length,
      ∀a : ℝ,partitionPoint 0 as pre.length ≤ Cmass*(M n).xs →
      ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U (W n) Q|)).sum ≤
        C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^3

def ActualSharpSourceFirstHighConstantOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (C : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let U:=retainedMassPrefixIndex (high n).val as
    ∀(mid tail : List PositiveMass),mid++tail=as →
      mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∃hs : mid.length<U,∃hU : U≤(mid++tail).length,
      ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
        [(nativeActualConstantState (mid++tail) 0 mid.length).projection (hs.le.trans hU)]).map
        (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U (W n) Q|)).sum ≤
        C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2

theorem actual_selected_bad_history_first_high_on_given_source_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0≤Cmass) (hA : A≤Cmass)
    (hcK : 0<cK) (hFirst : 0<cFirst) (hFirstLower : 2*cu*(Az+1)≤cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0≤Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃Ci Cc : ℝ,0<Ci ∧ 0<Cc ∧
      ActualSharpSourceFirstHighInitialOnEveryFinalNetAlong depth Cmass Ci M W w high outer ∧
      ActualSharpSourceFirstHighConstantOnEveryFinalNetAlong depth Cc M W w high outer := by
  have hWlim' : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0):=by
    have HE : W=(fun n=>(M n).canonicalDirectTestBandScale):=funext hcanonical
    simpa only [HE] using hWlim
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Ci,hCi,HI⟩:=actual_selected_bad_history_four_first_high_initial_rate_along
    depth Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hFirst hFirstLower dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory hWlim' hcompare
  obtain ⟨Cc,hCc,HC⟩:=actual_selected_bad_history_four_first_high_projected_constant_rate_along
    depth Cmass cK hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hFirst hFirstLower dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory hWlim' hcompare
  refine ⟨Ci,Cc,hCi,hCc,?_,?_⟩
  · filter_upwards [HI,Hcuts] with n hn hnCuts
    intro L us hus hret hmesh hstar hhigh houter
    filter_upwards [hn L us hus hret hmesh] with j hj
    dsimp only at hj ⊢
    obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,_,_,_,_,_,HK,_⟩:=
      hnCuts.finite_net_readout us hus hstar hhigh houter j
    intro pre mid tail hcut hindex
    have hs : pre.length+mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
      rw [hindex]
      exact Hs
    have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(pre++(mid++tail)).length:=by
      rw [hcut]
      exact HUV.le.trans HV
    refine ⟨hs,hU,?_⟩
    intro a hmi
    have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
    have Hmass' := Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
    have H:=hj pre.length (pre.length+mid.length) _ (by omega) hs
      (by simpa only [hcut] using hU) a
      (by simpa only [hcanonical n] using Hfirst) hmi
      (by simpa only [hindex,hcanonical n] using Hmass') (by simpa only [hindex,hcanonical n] using HK)
    let G : List PositiveMass→Prop:=fun bs=>
      ∀hU' : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤bs.length,
      ((nativeActualMinimumFourCenteredForest (M n) hs hU' (W n) depth
        [nativeActualInitialState bs pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourFirstHighError (M n)
          (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) (W n) Q|)).sum ≤
        Ci*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^3
    have HG : G (finiteCutMasses us j):=by
      intro hU'
      simpa only [hcanonical n] using H
    have HG' : G (pre++(mid++tail)):=hcut.symm ▸ HG
    exact HG' hU
  · filter_upwards [HC,Hcuts] with n hn hnCuts
    intro L us hus hret hmesh hstar hhigh houter
    filter_upwards [hn L us hus hret hmesh] with j hj
    dsimp only at hj ⊢
    obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,_,_,_,_,_,HK,_⟩:=
      hnCuts.finite_net_readout us hus hstar hhigh houter j
    intro mid tail hcut hindex
    have hs : mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
      rw [hindex]
      exact Hs
    have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(mid++tail).length:=by
      rw [hcut]
      exact HUV.le.trans HV
    refine ⟨hs,hU,?_⟩
    have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
    have Hmass' := Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
    have H:=hj mid.length _ hs (by simpa only [hcut] using hU)
      (by simpa only [hcanonical n] using Hfirst)
      (by simpa only [hindex,hcanonical n] using Hmass') (by simpa only [hindex,hcanonical n] using HK)
    let G : List PositiveMass→Prop:=fun bs=>
      ∀hU' : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤bs.length,
      ((nativeActualMinimumFourCenteredForest (M n) hs hU' (W n) depth
        [(nativeActualConstantState bs 0 mid.length).projection (hs.le.trans hU')]).map
        (fun Q=>|nativeActualOriginalFourFirstHighError (M n)
          (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) (W n) Q|)).sum ≤
        Cc*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2
    have HG : G (finiteCutMasses us j):=by
      intro hU'
      simpa only [hcanonical n] using H
    have HG' : G (mid++tail):=hcut.symm ▸ HG
    exact HG' hU

end OAI.SKFluctuations.Cavity
