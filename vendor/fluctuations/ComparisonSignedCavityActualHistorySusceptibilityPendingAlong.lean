module

public import ComparisonSignedCavityActualHistorySusceptibilityTaylorCategoriesAlong
public import ComparisonSignedCavityActualConstantPendingCategoryEnvelopeAlong
public import ComparisonSignedCavityActualHistoryConstantJointTaylorRate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem susceptibility_pending_envelope_absorption
    {gap W xs cS T Cb Cd old pending Taylor : ℝ}
    (hW : 0 < W) (hcS : 0 < cS) (hT : 0 ≤ T) (hxs : 0 ≤ xs) (hxW : xs ≤ W)
    (_hCd : 0 ≤ Cd)
    (Hgap : |gap| ≤ Cb*W^2+2*((T/cS)*old+|Taylor|/(cS*W)))
    (Hold : old ≤ Cd*W^2+pending) (HTaylor : |Taylor| ≤ W*xs^2) :
    |gap| ≤ (Cb+2*(T/cS)*Cd+2/cS)*W^2+2*(T/cS)*pending := by
  have Hxs : xs^2 ≤ W^2:=pow_le_pow_left₀ hxs hxW 2
  have HT : |Taylor|/(cS*W) ≤ W^2/cS:=by
    calc
      _ ≤ (W*xs^2)/(cS*W):=div_le_div_of_nonneg_right HTaylor (mul_pos hcS hW).le
      _ = xs^2/cS:=by field_simp
      _ ≤ W^2/cS:=div_le_div_of_nonneg_right Hxs hcS.le
  have HR:=mul_le_mul_of_nonneg_left Hold (div_nonneg hT hcS.le)
  have HH:=Hgap.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add HR HT)
    (by norm_num : (0:ℝ)≤2)))
  convert HH using 1
  ring

theorem exists_actual_selected_bad_history_susceptibility_pending_categories_along
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
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
      (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1)) ∧
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
            2*(T/cS)*nativeActualConstantSourcePendingCategoryEnvelope (M n) hs hU (W n) T cK depth := by
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_taylor_categories_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
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
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hcuts,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
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
