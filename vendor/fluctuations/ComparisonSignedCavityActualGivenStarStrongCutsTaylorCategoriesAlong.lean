module

public import ComparisonSignedCavityActualHistoryStrongCutsTaylorCategoriesAlong
public import ComparisonSignedCavityActualGivenStarStrongCutsCategoriesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_taylor_categories_along
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
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    {cK Cf Cwindow Ku Kv cFirst cKcut tau : ℝ}
    (hcK : 0 < cK) (hCf : 0 ≤ Cf) (hKu : 1 < Ku)
    (hFirst : 0 < cFirst) (hFirstLower : 2*cu*(Az+1) ≤ cFirst)
    (hcKcut : 0 < cKcut) (htau : 0 ≤ tau)
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf)
    (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cwindow (w n))
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k
      (actualSlowWindowExponent m delta/256) M W w)
    (high outer : ℕ → PositiveMass)
    (Hstrong : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx)
    (depth : ℕ)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK (actualSlowWindowExponent m delta/256)
      (actualMassSavingExponent m delta/32) tau depth M W w) :
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
              |nativeActualConstantSourceTaylorPart (M n) as star U|/(cS*W n)) := by
  have Hcuts:=Hstrong.mono (fun _ hn=>hn.toActualSharpSourceCutGeometry)
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cr,hCr,HR⟩:=actual_selected_bad_history_constant_source_remainder_on_given_cuts_along
    (by linarith : 0 ≤ Ku+1) hFirst hFirstLower hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hT.le hb hh Hhistory
    W (fun n=>Kv*W n) hcanonical hWlim (Filter.Eventually.of_forall hcompare) w high outer Hcuts
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_categories_along
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  refine ⟨Cb+2*Cr/cS,by positivity,?_⟩
  filter_upwards [HB,HR] with n hnB hnR
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnR Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjR
  dsimp only at hjB hjR ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  refine ⟨hs,hU,?_⟩
  exact susceptibility_bootstrap_remainder_reduction
    ((M n).hxs.trans_le (hxs n)) hcS (M n).hxs.le (hxs n) hCr.le HB hjR

end OAI.SKFluctuations.LaplaceWindowFormalization
