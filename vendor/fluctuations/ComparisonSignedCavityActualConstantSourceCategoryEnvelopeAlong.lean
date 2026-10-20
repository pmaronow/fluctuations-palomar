module

public import ComparisonSignedCavityActualConstantSourceCategoryEnvelope

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 30000000
variable {dim : ℕ → ℕ}

def ActualConstantSourceCategoryEnvelopeAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK rho C : ℝ)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    ∃hs : star < U,∃hU : U ≤ as.length,
    nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) Temp cK depth ≤
      C*((dim n+1:ℕ):ℝ)^(-rho)*(M n).xs^2+
        nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) Temp cK depth

theorem actual_constant_source_category_envelope_along_of_closed_rates
    {m delta eta cl cu Az C0 Ct D Bclock Temp cK cKcut cFirst A CK : ℝ}
    (depth : ℕ) (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta)
    (hcK : 0 < cK) (hcKcut : 0 < cKcut) (hCK : 0 < CK)
    (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (hupper : ∀ᶠn in atTop,actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val ≤ CK*W n)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A)
    (Hrates : ∀d : ℕ,∃Cg Cr Cf : ℝ,0 < Cg ∧ 0 < Cr ∧ 0 < Cf ∧
      ActualConstantSourceGaCurrentOnGivenCutsAlong d eta Cg M W w high outer ∧
      ActualConstantSourceGaRestorationOnGivenCutsAlong d Cr M W w high outer ∧
      ActualConstantSourceFirstHighOnGivenCutsAlong d Cf M W w high outer) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceCategoryEnvelopeAlong depth Temp cK
      (min eta (actualMassSavingExponent m delta/256)) C M W w high outer := by
  choose Cg Cr Cf hCg hCr hCf HG HR HF using Hrates
  let rho:=min eta (actualMassSavingExponent m delta/256)
  have hrho : 0 < rho:=lt_min heta (div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num))
  let L:=CK/(Real.exp (-4*Temp)*cK)
  have hL : 0 ≤ L:=by dsimp only [L];positivity
  let J:=fun d=>L*((1/2:ℝ)^(-rho)*Cg d+Cr d)+Cf d
  have hJ d : 0 ≤ J d:=by
    dsimp only [J]
    exact add_nonneg
      (mul_nonneg hL (add_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hCg d).le) (hCr d).le)) (hCf d).le
  let C:=((List.range depth).map J).sum+1
  have hC : 0 < C:=by
    have H : 0 ≤ ((List.range depth).map J).sum:=List.sum_nonneg (by
      intro x hx;obtain ⟨d,_,rfl⟩:=List.mem_map.mp hx;exact hJ d)
    dsimp only [C];linarith
  have HGN:=Filter.eventually_all.mpr (fun d : Fin depth=>HG d.val)
  have HRN:=Filter.eventually_all.mpr (fun d : Fin depth=>HR d.val)
  have HFN:=Filter.eventually_all.mpr (fun d : Fin depth=>HF d.val)
  refine ⟨C,hC,?_⟩
  filter_upwards [HGN,HRN,HFN,htotal,hupper,Hcuts,hdim.eventually (eventually_ge_atTop 1)]
    with n hnG hnR hnF hnTotal hnUpper hnCuts hn1
  intro Lnet us hus hret hmesh hstar hhigh houter
  have HGgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnG d Lnet us hus hret hmesh hstar hhigh houter)
  have HRgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnR d Lnet us hus hret hmesh hstar hhigh houter)
  have HFgrid:=Filter.eventually_all.mpr (fun d : Fin depth=>hnF d Lnet us hus hret hmesh hstar hhigh houter)
  filter_upwards [HGgrid,HRgrid,HFgrid] with j hjG hjR hjF
  dsimp only at hjG hjR hjF ⊢
  obtain ⟨Hs,HUV,HV,_,_,_,_,_,_,_,_,HK,_⟩:=hnCuts.finite_net_readout us hus hstar hhigh houter j
  have hU:=HUV.le.trans HV
  refine ⟨Hs,hU,?_⟩
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have HKupper : nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star ≤ CK*W n:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnUpper
  let N:=((dim n+1:ℕ):ℝ)
  let rate:=N^(-rho)*(M n).xs^2
  have hrate : 0 ≤ rate:=by dsimp only [rate,N];positivity
  have hN : 1 ≤ N:=by dsimp only [N];exact_mod_cast (show 1 ≤ dim n+1 by omega)
  have Hpow : N^(-(actualMassSavingExponent m delta/256)) ≤ N^(-rho):=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_right _ _))
  have HpowG:=actual_source_dimension_power_le hrho.le (min_le_left _ _) (dim n) hn1
  let BG:=fun d=>(1/2:ℝ)^(-rho)*Cg d*rate
  let BR:=fun d=>Cr d*rate
  let BF:=fun d=>Cf d*rate
  have GG d (hd : d < depth) : ((nativeActualMinimumFourCenteredForest (M n) Hs hU (W n) d
      (nativeActualConstantSourceChildren (M n) as star U Hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError (M n) U (W n) Q|)).sum ≤ BG d:=by
    obtain ⟨_,_,H⟩:=hjG ⟨d,hd⟩
    apply H.trans
    have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HpowG (hCg d).le) (sq_nonneg (M n).xs)
    convert HH using 1
    dsimp only [BG,rate,N]
    ring
  have RR d (hd : d < depth) : ((nativeActualMinimumFourCenteredForest (M n) Hs hU (W n) d
      (nativeActualConstantSourceChildren (M n) as star U Hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaRestorationError (M n) U (W n) Q|)).sum ≤ BR d:=by
    obtain ⟨_,_,H⟩:=hjR ⟨d,hd⟩
    apply H.trans
    have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow (hCr d).le) (sq_nonneg (M n).xs)
    convert HH using 1
    dsimp only [BR,rate,N]
    ring
  have FF d (hd : d < depth) : ((nativeActualMinimumFourCenteredForest (M n) Hs hU (W n) d
      (nativeActualConstantSourceChildren (M n) as star U Hs hU)).map
      (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U (W n) Q|)).sum ≤ BF d:=by
    obtain ⟨_,_,H⟩:=hjF ⟨d,hd⟩
    apply H.trans
    have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow (hCf d).le) (sq_nonneg (M n).xs)
    convert HH using 1
    dsimp only [BF,rate,N]
    ring
  have H:=actual_minimum_constant_source_category_envelope_le (M n) hnTotal hW hcKcut hcK ho
    Hs hU HK HKupper depth BG BR BF GG RR FF
  apply H.trans
  apply add_le_add _ le_rfl
  change ((List.range depth).map (fun d=>L*(BG d+BR d)+BF d)).sum ≤ C*N^(-rho)*(M n).xs^2
  have HE : ((List.range depth).map (fun d=>L*(BG d+BR d)+BF d)).sum=
      ((List.range depth).map J).sum*rate:=by
    rw [←List.sum_map_mul_right]
    congr 1
    apply List.map_congr_left
    intro d _
    dsimp only [J,BG,BR,BF]
    ring
  rw [HE]
  have HH:=mul_le_mul_of_nonneg_right (show ((List.range depth).map J).sum ≤ C by dsimp only [C];linarith) hrate
  simpa only [rate,mul_assoc] using HH

theorem actual_selected_bad_history_constant_source_category_envelope_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cKcut cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 1 ≤ Cmass) (hA : A ≤ Cmass)
    (hcKcut : 0 < cKcut) (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
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
      (high n) (outer n) (radius n) cFirst cKcut A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceCategoryEnvelopeAlong depth Temp cK
      (min eta (actualMassSavingExponent m delta/256)) C M W w high outer := by
  have Hrates d : ∃Cg Cr Cf : ℝ,0 < Cg ∧ 0 < Cr ∧ 0 < Cf ∧
      ActualConstantSourceGaCurrentOnGivenCutsAlong d eta Cg M W w high outer ∧
      ActualConstantSourceGaRestorationOnGivenCutsAlong d Cr M W w high outer ∧
      ActualConstantSourceFirstHighOnGivenCutsAlong d Cf M W w high outer:=by
    obtain ⟨Cg,Cf,hCg,hCf,HG,HF⟩:=actual_selected_bad_history_constant_source_rates_on_given_cuts_along
      d Cmass hCm hA hcKcut hc hcouter heta hgap hm hdelta hroom hcl hcu hAz hC0 hCt
      hCcal hc0 hmargin hcapmargin hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
      W radius hcanonical hWlim hcompare saving hsaving w Hmixed high outer Hcuts
    obtain ⟨Cr,hCr,HR⟩:=actual_selected_bad_history_constant_source_restoration_on_given_cuts_along
      d Cmass (zero_le_one.trans hCm) hA hcKcut hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt
      hc0 hmargin hcapmargin hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
      W radius hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
    exact ⟨Cg,Cr,Cf,hCg,hCr,hCf,HG,HR,HF⟩
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have hxs n : (M n).xs ≤ W n:=
    (M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  have Hupper : ∀ᶠn in atTop,actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val ≤
      (CK*(1+Cmass))*W n:=by
    filter_upwards [hdim.eventually HK,Hsource,Hcuts] with n hn hs hcuts
    have hu : (w n).star.val∈Icc (0:ℝ) 1:=
      ⟨(w n).star.property.le,hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_le_one)⟩
    have hW : 0 ≤ W n:=((M n).hxs.trans_le (hxs n)).le
    have Hmass : (w n).star.val ≤ Cmass*W n:=
      (hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_scale)).trans
        (mul_le_mul_of_nonneg_right hA hW)
    have Hsize : (M n).xs+(w n).star.val ≤ (1+Cmass)*W n:=by linarith [hxs n]
    exact (hn (M n) hs _ hu).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hsize hCK.le)
  exact actual_constant_source_category_envelope_along_of_closed_rates depth heta hm hdelta hcK hcKcut
    (mul_pos hCK (by linarith)) hdim M W radius hxs w high outer
    (Htotal.mono (fun _ h=>h.1)) Hupper Hcuts Hrates

end OAI.SKFluctuations.Cavity
