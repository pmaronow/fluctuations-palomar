module

public import ComparisonSignedCavityActualInitialSeedReadout
public import ComparisonSignedCavityActualHistoryInitialSavedNonLowAlong
public import ComparisonSignedCavityActualHistoryClosedInitialFeedbackAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualInitialResidualModuloThermalOnStrongCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (A : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
    ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let U:=retainedMassPrefixIndex (high n).val as
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
        partitionPoint 0 as pre.length ≤ A*(M n).xs →
      ∃hs : pre.length+mid.length<U,∃hU : U ≤ (pre++(mid++tail)).length,
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail))
        pre.length (pre.length+mid.length) 0 (by omega)
      |nativeActualMinimumFourResidualSum (M n) hs hU (W n) depth [st]| ≤ err n*(M n).xs^3+
        ((List.range depth).map (fun d=>nativeActualInitialThermalCategoryEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d [st]))).sum

theorem actual_selected_bad_history_initial_residual_modulo_thermal_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c cK A Tstar Lwin Cwindow Cj : ℝ}
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
    (saving : ℝ) (hsaving : 0 < saving) (hCj : 0 ≤ Cj)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hsquare : ∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w)
    (HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cK A) :
    ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
      ActualInitialResidualModuloThermalOnStrongCutsAlong depth A err M W w high outer := by
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
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  have HP (degree : ℕ) (hd : 0 < degree):=
    actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along degree hd
      hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf A (zero_le_one.trans hA)
      dim hdim M W hxs hWlim Hsource w (Hsquare (degree-1))
  have Hsharp:=eventually_actual_sharp_star_inherited_endpoint_second_along
    hm hdelta hC0 hCf dim hdim M W hcanonical hWlim w Hsource hw
  have hsharp : 0 < actualMassSavingExponent m delta/32:=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have Hnum:=actual_same_star_initial_four_numeric_inputs_along hm hC0 hTemp hsaving hsharp hcK
    A dim hdim M W hxs (Htotal.mono fun _ hn=>hn.1) (Htotal.mono fun _ hn=>hn.2)
    w (Hcuts.mono fun _ hn=>hn.clock_star) HP Hsharp
  obtain ⟨eP,heP,hPlim,Hpair⟩:=actual_calibrated_initial_pair_feedback_residual_along
    (Temp:=Temp) depth hsaving.le hsharp hcK hCj hdim M W radius hxs w high outer Hcuts HJ
    (fun d=>Hnum.2.2 0 d 2)
  obtain ⟨eF,heF,hFlim,Hfrozen⟩:=actual_history_initial_frozen_child_envelope_of_pair_budgets_along
    depth hm hC0 hTemp hsaving hcK hdim root M epsilon shell hepsilon hb hh Hhistory
    W radius hxs w high outer Hcuts (fun d _=>HP (d+2) (by omega))
  have HN d:=actual_selected_bad_history_initial_saved_nonLOW_on_given_cuts_along
    d hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W radius hcanonical hWlim hcompare
    saving hsaving.le w high outer Hmixed Hcuts
  choose eN heN hNlim HN using HN
  have HG d:=actual_inherited_initial_three_Gamma_on_given_cuts_along
    d hA hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hCcal hdim
    M W radius hcanonical hWlim Hsource (fun n=>(M n).xs) (Eventually.of_forall fun _=>le_rfl)
    (Eventually.of_forall hxs) (Eventually.of_forall hcompare) Hshell saving hsaving.le w high outer hw Hmixed Hcuts
  choose eG heG hGlim HG using HG
  have HL d:=actual_inherited_initial_longitudinal_on_given_cuts_along
    d (zero_le_one.trans hA) hcK hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hCf hdim
    M W radius hcanonical hWlim Hsource (Eventually.of_forall hcompare) Hshell w high outer Hcuts
  choose eL heL hLlim HL using HL
  let ec d n:=eN d n+eG d n+eL d n
  let err n:=eP n+eF n+((List.range depth).map (fun d=>ec d n)).sum
  have Hclim d : Tendsto (ec d) atTop (𝓝 0):=by
    simpa only [ec,zero_add] using ((hNlim d).add (hGlim d)).add (hLlim d)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>ec d n)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil=>simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons d ds ih=>simpa only [List.map_cons,List.sum_cons,zero_add] using (Hclim d).add ih
  refine ⟨err,?_,?_,?_⟩
  · intro n
    dsimp only [err,ec]
    exact add_nonneg (add_nonneg (heP n) (heF n)) (List.sum_nonneg (by
      intro a ha;obtain ⟨d,_,rfl⟩:=List.mem_map.mp ha
      exact add_nonneg (add_nonneg (heN d n) (heG d n)) (heL d n)))
  · simpa only [err,zero_add] using (hPlim.add hFlim).add (Hlim (List.range depth))
  · have HNs:=Filter.eventually_all.mpr (fun d : Fin depth=>HN d.val)
    have HGs:=Filter.eventually_all.mpr (fun d : Fin depth=>HG d.val)
    have HLs:=Filter.eventually_all.mpr (fun d : Fin depth=>HL d.val)
    filter_upwards [Hpair,Hfrozen,HNs,HGs,HLs,Hcuts,Htotal] with n hp hf hn hg hl hcuts htotal
    intro L us hus hret hmesh hstar hhigh houter hnodes
    have HNg:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter)
    have HGg:=Filter.eventually_all.mpr (fun d : Fin depth=>hg d L us hus hret hmesh hstar hhigh houter)
    have HLg:=Filter.eventually_all.mpr (fun d : Fin depth=>hl d L us hus hret hmesh hstar hhigh houter)
    filter_upwards [hp L us hus hret hmesh hstar hhigh houter hnodes,
      hf L us hus hret hmesh hstar hhigh houter,HNg,HGg,HLg] with jGrid hjP hjF hjN hjG hjL
    dsimp only at hjP hjF hjN hjG hjL ⊢
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    obtain ⟨hs,HUV,HV,_,_,_,_,_,_,_,_,HstarK,_⟩:=hcuts.finite_net_readout us hus hstar hhigh houter jGrid
    have hU:=HUV.le.trans HV
    obtain ⟨_,_,hjP⟩:=hjP
    obtain ⟨_,_,hjF⟩:=hjF
    intro pre mid tail hparts hindex hmid hmi
    let old:=pre++(mid++tail)
    let s:=pre.length+mid.length
    have hi : pre.length ≤ s:=by dsimp only [s];omega
    have HI : s<U:=by dsimp only [s];rw [hindex];exact hs
    have HU : U ≤ old.length:=by dsimp only [old];rw [hparts];exact hU
    have hi0 : pre.length ≤ star:=by dsimp only [star,as];rw [←hindex];omega
    let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) old pre.length s 0 (hi.trans (HI.le.trans HU))
    refine ⟨HI,HU,?_⟩
    have HPa : nativeActualInitialPairFeedbackEnvelope (M n) hs hU (W n) Temp cK depth
        [nativeActualInitialState as pre.length star 0 (hi0.trans (hs.le.trans hU))] ≤eP n*(M n).xs^3:=by
      have H:=hjP pre.length hi0 (M n).xs le_rfl (hxs n) hmi
      apply H.trans_eq
      ring
    have HPb:=actual_initial_seed_function_reindex as old hparts star s hindex hi0 hs hU hi HI HU
      (fun _ _ hs hU rows=>nativeActualInitialPairFeedbackEnvelope (M n) hs hU (W n) Temp cK depth rows) _ HPa
    have HFa : nativeActualFourFrozenChildResidualEnvelope (M n) hs hU (W n) depth
        [nativeActualInitialState as pre.length star 0 (hi0.trans (hs.le.trans hU))] ≤eF n*(M n).xs^3:=by
      have H:=hjF pre.length hi0 (M n).xs le_rfl (hxs n) hmi
      apply H.trans_eq
      ring
    have HFb:=actual_initial_seed_function_reindex as old hparts star s hindex hi0 hs hU hi HI HU
      (fun _ _ hs hU rows=>nativeActualFourFrozenChildResidualEnvelope (M n) hs hU (W n) depth rows) _ HFa
    have Hrow d (hd : d∈List.range depth) :
        nativeActualInitialSavedNonLowEnvelope (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d [st])+
        nativeActualThreeGammaCategoryEnvelope (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d [st])+
        nativeActualInitialLongitudinalEnvelope (M n) U (W n)
            (nativeActualMinimumFourCenteredForest (M n) HI HU (W n) d [st]) ≤ ec d n*(M n).xs^3:=by
      obtain ⟨_,_,HN0⟩:=hjN ⟨d,List.mem_range.mp hd⟩ pre mid tail hparts hindex hmid hmi
      obtain ⟨_,_,HG0⟩:=hjG ⟨d,List.mem_range.mp hd⟩ pre mid tail hparts hindex hmid hmi
      obtain ⟨_,_,HL0⟩:=hjL ⟨d,List.mem_range.mp hd⟩
      have HLa:=HL0 pre.length hi0 (M n).xs le_rfl (hxs n) hmi
      have HLb:=actual_initial_seed_function_reindex as old hparts star s hindex hi0 hs hU hi HI HU
        (fun _ _ hs hU rows=>nativeActualInitialLongitudinalEnvelope (M n) U (W n)
          (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d rows)) _ HLa
      have HB:=add_le_add (add_le_add (HN0 0) (HG0 0)) HLb
      apply HB.trans_eq
      dsimp only [ec]
      ring
    have HS:=List.sum_le_sum Hrow
    rw [List.sum_map_add,List.sum_map_add,List.sum_map_mul_right] at HS
    have hvalid : ∀Q∈[st],NativeActualResourceGenerated pre.length s U [.initial] Q.generation Q.tree Q.term:=by
      intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ
      exact .physical (.seed old HU 0 .initial (Or.inl rfl) (hi.trans (HI.le.trans HU)))
    have HO : MassOrdered 0 old:=by rw [show old=as from hparts];exact finiteCutMasses_ordered us hus jGrid
    have HK : cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf old s:=by
      dsimp only [old,s];rw [hparts,hindex];exact HstarK
    have Hres:=actual_minimum_four_residual_abs_le_initial_normalized_envelope (M n) htotal.1
      ((M n).hxs.trans_le (hxs n)) hcK HO hi HI HU HK [st] hvalid depth
    rw [actual_initial_normalized_residual_envelope_eq] at Hres
    have Hsaved:=add_le_add (add_le_add HPb HFb) HS
    apply Hres.trans
    dsimp only [err]
    nlinarith only [Hsaved]

end OAI.SKFluctuations.Cavity
