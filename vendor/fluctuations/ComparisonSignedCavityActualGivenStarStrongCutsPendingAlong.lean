module

public import ComparisonSignedCavityActualHistoryStrongCutsPendingAlong
public import ComparisonSignedCavityActualGivenStarStrongCutsTaylorCategoriesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem actual_given_sharp_star_strong_cuts_pending_along
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
            2*(T/cS)*nativeActualConstantSourcePendingCategoryEnvelope (M n) hs hU (W n) T cK depth := by
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
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨err,herr,HTaylor⟩:=actual_selected_bad_history_constant_joint_Taylor_rate_along
    (Ccompare:=Ccal^2) (Ku+1) hT.le (by linarith) (sq_nonneg Ccal)
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hFirst hFirstLower hmargin hcapmargin
    dim hdim root M epsilon shell hepsilon hb hh Hhistory W hcanonical hWlim w hw
    (Filter.Eventually.of_forall hcompare)
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨Cb,hCb,HB⟩:=actual_given_sharp_star_strong_cuts_taylor_categories_along
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
      hcK hCf hKu hFirst hFirstLower hcKcut htau Hsource w hw Hmixed high outer Hstrong depth Hknown
  obtain ⟨Cd,hCd,HD⟩:=actual_selected_bad_history_constant_pending_category_envelope_along
    depth (Ku+1) (by linarith) le_rfl hcKcut hcK hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin hdim root M epsilon shell hepsilon hT.le hb hh Hhistory
    W (fun n=>Kv*W n) hcanonical hWlim w high outer Hcuts
  refine ⟨Cb+2*(T/cS)*Cd+2/cS,by positivity,?_⟩
  filter_upwards [HB,HD,HTaylor,Herr,Hcuts] with n hnB hnD hnT hne hnCuts
  intro Lnet us hus hret hmesh hstar hhigh houter
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnD Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hstar hret hmesh] with j hjB hjD hjT
  dsimp only at hjB hjD hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HD⟩:=hjD
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  obtain ⟨_,HUV,HV,Hlo,_,Houter,_,_,_,_,_,_,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  have Hupper : partitionPoint 0 as U≤ min ((Ku+1)*W n) 1:=by
    refine le_min ?_ (partitionPoint_mem as ho U).2
    exact (partitionPoint_mono as ho HUV.le).trans Houter
  have HT:=hjT U hs hU Hlo Hupper
  have HS : (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k))=
      nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as:=by
    funext k
    exact native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone (partitionPoint_mem as ho k)
  change |nativeActualJointRestoredForwardTaylorError (dim n) _ U _ _ _
    (fun k=>orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as k)) _ _ _ _|≤_ at HT
  rw [HS] at HT
  change |nativeActualConstantSourceTaylorPart (M n) as star U|≤err n*(W n*(M n).xs^2) at HT
  have HT' : |nativeActualConstantSourceTaylorPart (M n) as star U|≤W n*(M n).xs^2:=
    HT.trans ((mul_le_mul_of_nonneg_right hne (mul_nonneg (hW n).le (sq_nonneg _))).trans_eq (one_mul _))
  have Hpow : ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)≤1:=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dim n)))
      (by norm_num)
  have Hrate : Cd*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2≤Cd*(W n)^2:=by
    have H1:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hpow hCd.le) (sq_nonneg (M n).xs)
    simp only [mul_one] at H1
    exact H1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (M n).hxs.le (hxs n) 2) hCd.le)
  have HD':=HD.trans (add_le_add Hrate le_rfl)
  refine ⟨hs,hU,?_⟩
  exact susceptibility_pending_envelope_absorption (hW n) hcS hT.le (M n).hxs.le (hxs n)
    hCd.le HB HD' HT'

end OAI.SKFluctuations.LaplaceWindowFormalization
