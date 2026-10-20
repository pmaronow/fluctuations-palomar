module

public import ComparisonSignedCavityActualConstantSourceFeedbackAbsorption
public import ComparisonSignedCavityActualHistorySusceptibilitySourceCuts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_susceptibility_by_other_sources_along
    {m delta cl cu Az C0 Ct D Bclock T L Cwindow c0 A cFirst cKcut cK gamma sharpSaving terminalSaving : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0≤1) (hA : 0≤A)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hcK : 0 < cK) (hgamma : 0≤gamma) (hsharp : 0 < sharpSaving) (hterminal : 0≤terminalSaving)
    (depth : ℕ) (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0≤epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ → ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cwindow (w n))
    (high outer : ℕ → PositiveMass) (radius : ℕ → ℝ)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cKcut A)
    (Hknown : ActualConstantSourceKnownEnvelopeAlong T cK gamma sharpSaving terminalSaving depth M W w) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
      (∀u∈us,u.val≤1) → (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
        let as:=finiteCutMasses us j
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex (high n).val as
        ∃hs : star < U,∃hU : U≤as.length,
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        let cS:=3*(starMassBandConstant cu Az/cu)/4
        |(T-epsilon)*chi^2-1|≤C*(W n)^2+
          2*((T/cS)*nativeActualConstantSourceErrorEnvelope (M n) hs hU (W n) T cK depth+
            |nativeActualConstantSourceRemainder (M n) as star U|/(cS*W n)) := by
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cs,hCs,Hsus⟩:=actual_selected_bad_history_susceptibility_on_source_cuts_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hA hmargin hcapmargin
    dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W hxs hWlim w hw high outer radius Hcuts
  obtain ⟨Cb,hCb,Hbond⟩:=actual_selected_bad_history_susceptibility_coefficient_along
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim w hw
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  let cS:=3*(starMassBandConstant cu Az/cu)/4
  have hcS : 0 < cS:=by
    have H:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
    dsimp only [cS]
    positivity
  let coefficient:=(T/cS)*(6*(depth:ℝ)/(Real.exp (-4*T)*cK))
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim)
  have Hpow : Tendsto (fun n=>((dim n+1:ℕ):ℝ)^(-sharpSaving/2)) atTop (𝓝 0):=by
    convert (tendsto_rpow_neg_atTop (half_pos hsharp)).comp HN using 1
    funext n
    simp only [Function.comp_apply,neg_div]
  have Hsmall : ∀ᶠn in atTop,coefficient*((dim n+1:ℕ):ℝ)^(-sharpSaving/2)≤1/2:=by
    have H:=Hpow.const_mul coefficient
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2))
  let C:=2*(Cs+(T/cS)*(6*(depth:ℝ)+13)+Cb)+1
  have hT : 0≤T:=by linarith
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsus,Hbond,Htotal,Hknown,Hcuts,Hsmall] with n hnS hnB hnT hnKnown hnCuts hnSmall
  intro us hus hstar hhigh houter
  filter_upwards [hnS us hus hstar hhigh houter,hnKnown us hus hstar] with j hjS hjKnown
  dsimp only at hjS hjKnown ⊢
  obtain ⟨hs,hUV,hV,_⟩:=hnCuts.finite_net_readout us hus hstar hhigh houter j
  have hU:=hUV.le.trans hV
  refine ⟨hs,hU,?_⟩
  have ho:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have H:=actual_minimum_constant_source_susceptibility_feedback_absorption (M n) hs hU ho hnT.1
    hW (hxs n) hcK hcS hgamma hterminal depth (hjKnown _ hs hU) hjS
    (hnB _ ho (finiteCutMasses_nodes us j hstar) _ hs hU) hnSmall
  apply H.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have HB:=mul_le_mul_of_nonneg_right hnSmall hCb.le
  dsimp only [C,coefficient,cS] at HB ⊢
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
