module

public import ComparisonSignedCavityActualConstantFullB0EnvelopeSavingAlong
public import ComparisonSignedCavityActualStrongSharpSourceCuts
public import ComparisonSignedCavityActualHistoryStrongCutsB0CategoryAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_susceptibility_strong_cuts_closed_along
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
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
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |(T-epsilon)*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2 := by
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_susceptibility_strong_cuts_b0_category_along
      Rmacro Cx hmacro hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  dsimp only at Hbootstrap
  have hT : 0 < T:=by linarith
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hshell : ∀ᶠn in atTop,∃(Tbase eps sh : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase eps sh ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u):=by
    filter_upwards [Hps] with n hn
    exact ⟨T,epsilon,shell,((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)),hn.2.1,hn.2.2⟩
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cbond,hCbond,Hbond⟩:=actual_selected_bad_history_susceptibility_coefficient_along
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim w hw
  refine ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,?_⟩
  intro depth hd
  obtain ⟨Cb,hCb,HB⟩:=Hbootstrap depth hd
  obtain ⟨err,herr,HT⟩:=actual_inherited_constant_full_b0_envelope_saving_along
    (Ccal:=Ccal) depth (by linarith : 1 ≤ Ku+1) hcK hcKcut hmacro hRhalf hCx
    hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf hCcal
    hdim M W (fun n=>Kv*W n) hcanonical hWlim Hsource (Filter.Eventually.of_forall hcompare)
    Hshell w high outer hw Hstrong
  have Herr:=herr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨Cb+2*(T/cS)+Cbond,by positivity,?_⟩
  filter_upwards [HB,HT,Herr,Hbond] with n hnB hnT hne hnBond
  intro Lnet us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hnB Lnet us hus hret hmesh hstar hhigh houter,
    hnT Lnet us hus hret hmesh hstar hhigh houter hnodes] with j hjB hjT
  dsimp only at hjB hjT ⊢
  obtain ⟨hs,hU,HB⟩:=hjB
  obtain ⟨_,_,HT⟩:=hjT
  have Hsmall : err n*(M n).xs^2 ≤ (W n)^2:=by
    apply (mul_le_mul_of_nonneg_right hne (sq_nonneg (M n).xs)).trans
    simpa only [one_mul] using pow_le_pow_left₀ (M n).hxs.le (hxs n) 2
  have Hpaid:=HT.trans Hsmall
  have Hgap : |(T-epsilon)*
      (scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us j)
        (relocatedClock (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) 0
          (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us j))))).H 0 0^2-1| ≤
      (Cb+2*(T/cS))*(W n)^2:=by
    apply HB.trans
    have H:=mul_le_mul_of_nonneg_left Hpaid (show 0 ≤ 2*(T/cS) by positivity)
    have H':=add_le_add_left H (Cb*(W n)^2)
    convert H' using 1 <;> ring
  have HBond:=hnBond (finiteCutMasses us j) (finiteCutMasses_ordered us hus j)
    (finiteCutMasses_nodes us j hstar) _ hs hU
  refine ⟨hs,hU,?_,?_⟩
  · apply Hgap.trans
    nlinarith [sq_nonneg (W n)]
  · apply HBond.trans
    nlinarith only [Hgap]

end OAI.SKFluctuations.LaplaceWindowFormalization
