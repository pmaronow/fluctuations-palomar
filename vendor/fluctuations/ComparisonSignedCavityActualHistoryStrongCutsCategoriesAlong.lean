module

public import ComparisonSignedCavityActualHistorySusceptibilityCategoriesAlong
public import ComparisonSignedCavityActualStrongSharpSourceCuts
public import ComparisonSignedCavityActualHistoryStrongCutsBootstrapAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_categories_along
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0  <  L) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4  <  3*m-99*delta) (hcapmargin : 100*delta  <  (1:ℝ)/3+m)
    (hgapmargin : 0  <  9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0  <  shell) (hTemp : 0  <  T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃hs : star < U,∃hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          let cS:=3*(starMassBandConstant cu Az/cu)/4
          |(T-epsilon)*chi^2-1|≤C*(W n)^2+
            2*((T/cS)*nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth+
              |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_bootstrap_along
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hfactor : 0 ≤ T/cS:=div_nonneg hT.le hcS.le
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hsaving : 0 ≤ actualSlowWindowExponent m delta/256:=
    (div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)).le
  let rho:=min m (actualMassSavingExponent m delta/256)
  have hrho : 0 ≤ rho:=le_min hm.le (div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num))
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨Ce,hCe,HE⟩:=actual_selected_bad_history_constant_source_category_envelope_along
    (eta:=m) depth (Ku+1) (by linarith) le_rfl hcKcut hcK hFirst hFirstLower hm (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin hdim
    root M epsilon shell hepsilon hT.le hb hh Hhistory W (fun n=>Kv*W n)
    hcanonical hWlim hcompare (actualSlowWindowExponent m delta/256) hsaving w Hmixed high outer Hcuts
  let C:=Cb+2*(T/cS)*Ce
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,HE] with n hnB hnE
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB us hus hstar hhigh houter,hnE Lnet us hus hret hmesh hstar hhigh houter]
    with j hjB hjE
  dsimp only at hjB hjE ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HE⟩:=hjE
  refine ⟨hs,hU,?_⟩
  let N:=((dim n+1:ℕ):ℝ)
  have hN : 1 ≤ N:=by dsimp only [N];exact_mod_cast (show 1 ≤ dim n+1 by omega)
  have hpow : N^(-rho) ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hrho)
  have hxs2 : (M n).xs^2 ≤ (W n)^2:=by nlinarith [(M n).hxs,hxs n]
  have Hrate : Ce*N^(-rho)*(M n).xs^2 ≤ Ce*(W n)^2:=by
    have H:=(mul_le_mul_of_nonneg_right hpow (sq_nonneg (M n).xs)).trans (by simpa using hxs2)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H hCe.le
  have HE' : nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth ≤
      Ce*(W n)^2+nativeActualConstantSourceRemainingCategoryEnvelope (M n) hs hU (W n) T cK depth:=
    HE.trans (add_le_add Hrate le_rfl)
  have HH:=mul_le_mul_of_nonneg_left HE' hfactor
  dsimp only [C,cS] at HH ⊢
  nlinarith only [HB,HH]

end OAI.SKFluctuations.LaplaceWindowFormalization
