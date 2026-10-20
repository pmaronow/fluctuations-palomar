module

public import ComparisonSignedCavityActualHistoryStrongCutsPostTaylorAlong
public import ComparisonSignedCavityActualGivenStarStrongCutsPendingAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_post_taylor_along
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
            2*(T/cS)*nativeActualConstantSourcePostTaylorCategoryEnvelope (M n) hs hU (W n) T cK depth := by
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
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hshell : ∀ᶠn in atTop,∃(Tbase ep sh : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase ep sh ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u):=by
    filter_upwards [Hps] with n hn
    exact ⟨T,epsilon,shell,((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)),hn.2.1,hn.2.2⟩
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_pending_along
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_post_Taylor_envelope_along
    depth Bclock T Cf (Ku+1) cK cKcut hT.le hCf (by linarith) hcK hcKcut
    (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hFirst hFirstLower
    dim hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource
    (Filter.Eventually.of_forall hcompare) Hshell w high outer hw Hcuts
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS),by positivity,?_⟩
  filter_upwards [HB,HT,Herr] with n hnB hnT hne
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans (add_le_add le_rfl Hsmall)
  refine ⟨hs,hU,?_⟩
  apply HB.trans
  have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
  have H':=add_le_add_left H (Cb*(W n)^2)
  convert H' using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
