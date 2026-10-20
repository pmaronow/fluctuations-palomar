module

public import ComparisonSignedCavityActualInitialSavedNonLowEnvelope
public import ComparisonSignedCavityActualInitialRestoredGaOnCutsAlong
public import ComparisonSignedCavityActualInitialDeletedSiteOnCutsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualHistoryInitialSavedNonLowOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      ∀seedMass : ℝ,
        nativeActualInitialSavedNonLowEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
            [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length)
              seedMass (by omega)]) ≤ err n*(M n).xs^3

theorem actual_selected_bad_history_initial_saved_nonLOW_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A : ℝ}
    (depth : ℕ) (hA : 1 ≤ A) (hcK : 0 < cK) (hc : 0 < c)
    (hcouter : 2*cu*(Az+1) ≤ c)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualHistoryInitialSavedNonLowOnGivenCutsAlong depth A err M W w high outer := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim
    root M epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u):=by
    filter_upwards [Hps] with n hn
    exact ⟨Temp,epsilon,shell,_,hn.2.1,hn.2.2⟩
  have hxs n : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨CF,_,hCF,_,HF,_⟩:=actual_selected_bad_history_first_high_on_given_source_cuts_along
    depth A (zero_le_one.trans hA) le_rfl hcK hc hcouter
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin hdim
    root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim
    (Eventually.of_forall hcompare) w high outer Hcuts
  obtain ⟨CG,hCG,HG0⟩:=eventually_inherited_same_star_four_Ga_current_initial_along
    (eta:=m) hdim depth A cK hA hcK hm hm hdelta hroom (by linarith)
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare Hsource saving hsaving w Hmixed
  have HG:=HG0.on_sharp_source_cuts hxs le_rfl Hcuts
  obtain ⟨eR,heR,eRlim,HR⟩:=actual_inherited_initial_restored_Ga_on_given_cuts_along
    depth hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal
    hdim M W radius hcanonical hWlim Hsource (Eventually.of_forall hcompare) Hshell w high outer Hcuts
  obtain ⟨eD,heD,eDlim,HD⟩:=actual_inherited_initial_deleted_site_on_given_cuts_along
    depth hA hcK hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf
    hdim M W radius hcanonical hWlim Hsource w high outer Hcuts
  let eF n:=CF*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  let eG n:=CG*(dim n:ℝ)^(-m)
  let err n:=eF n+eG n+eR n+eD n
  have eFlim : Tendsto eF atTop (𝓝 0):=by
    have H:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
      (by norm_num : (0:ℝ)<256))).comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
    simpa only [eF,Function.comp_def,mul_zero] using H.const_mul CF
  have eGlim : Tendsto eG atTop (𝓝 0):=by
    simpa only [eG,Function.comp_def,mul_zero] using
      ((tendsto_rpow_neg_atTop hm).comp (tendsto_natCast_atTop_atTop.comp hdim)).const_mul CG
  have herr n : 0 ≤ err n:=by
    dsimp only [err,eF,eG]
    exact add_nonneg (add_nonneg (add_nonneg (by positivity) (by positivity)) (heR n)) (heD n)
  have errlim : Tendsto err atTop (𝓝 0):=by
    simpa only [err,zero_add] using ((eFlim.add eGlim).add eRlim).add eDlim
  refine ⟨err,herr,errlim,?_⟩
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [HF,HG,HR,HD,Hcuts,Hsource,HW] with n hnF hnG hnR hnD hcuts hsClocks hW1
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hnF L us hus hret hmesh hstar hhigh houter,
    hnG L us hus hret hmesh hstar hhigh houter,
    hnR L us hus hret hmesh hstar hhigh houter,
    hnD L us hus hret hmesh hstar hhigh houter] with jGrid hjF hjG hjR hjD
  dsimp only at hjF hjG hjR hjD ⊢
  let as:=finiteCutMasses us jGrid
  let U:=retainedMassPrefixIndex (high n).val as
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  intro pre mid tail hcut hindex hmid hmi
  obtain ⟨HI,HU,HF⟩:=hjF pre mid tail hcut hindex
  obtain ⟨_,_,HG⟩:=hjG pre mid tail hcut hindex hmid
  obtain ⟨_,_,HR⟩:=hjR pre mid tail hcut hindex hmid hmi
  obtain ⟨_,_,HD⟩:=hjD pre mid tail hcut hindex hmid hmi
  refine ⟨HI,HU,?_⟩
  intro seedMass
  let old:=pre++(mid++tail)
  let i:=pre.length
  let star:=pre.length+mid.length
  have hi : i ≤ star:=by dsimp only [i,star];omega
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old i star seedMass (hi.trans (HI.le.trans HU))
  let rows:=nativeActualMinimumFourCenteredForest (M n) HI HU (W n) depth [st]
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed old HU seedMass .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
  have Hvalid : ∀Q∈rows,NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term:=by
    apply nativeActualFourCenteredForest_valid
    intro Q hQ
    have HQ : Q=st:=List.mem_singleton.mp hQ
    subst Q
    exact hP
  have ho : MassOrdered 0 old:=by dsimp only [old];rw [hcut];exact finiteCutMasses_ordered us hus jGrid
  have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old star:=by
    dsimp only [old,star];rw [hcut,hindex];exact HstarK
  have HF' : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U (W n) Q|)).sum ≤
      eF n*(M n).xs^3:=by exact HF seedMass hmi
  have HG' : (rows.map (fun Q=>|nativeActualOriginalFourGaCurrentError (M n) U (W n) Q|)).sum ≤
      eG n*(M n).xs^3:=by
    apply (HG seedMass (M n).xs le_rfl (hxs n) hmi).trans_eq
    dsimp only [eG]
    ring
  have H:=actual_initial_saved_nonLOW_envelope_le (M n) hCf hsClocks ((hxs n).trans hW1)
    ho hi HI HU hW hcK HK rows Hvalid HG' (HR seedMass) HF' (HD seedMass)
  apply H.trans_eq
  dsimp only [err]
  ring

end OAI.SKFluctuations.Cavity
