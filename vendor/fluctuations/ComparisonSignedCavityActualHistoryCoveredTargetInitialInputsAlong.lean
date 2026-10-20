module

public import ComparisonSignedCavityActualHistoryCoveredTargetSusceptibilityAlong
public import ComparisonSignedCavityActualHistoryClosedTargetInitialJointAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_covered_target_initial_inputs_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 ≤ Atarget)
    (Rmacro Cx : ℝ) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hCx : 0 < Cx)
    (hm : 0  <  m) (hdelta : 0  <  delta) (hroom : delta  <  3*m)
    (hcl : 0  <  cl) (hcu : 0  <  cu) (hAz : 0 ≤ Az) (hC0 : 0  <  C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0  <  c0) (hc01 : c0 ≤ 1)
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
    0 < saving ∧∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) (Atarget+1) Cwindow (w n)) ∧
      (∀ᶠn in atTop,Atarget*(M n).xs < (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
        (actualMassSavingExponent m delta/32) M W w ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
        ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∃thresholdI : ℕ,0 < thresholdI ∧ ∃savingI : ℝ,0 < savingI ∧
        ∀depth : ℕ,thresholdI ≤ depth → ActualTargetInitialResidualApproxAlong depth savingI Cmass M W w) ∧
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
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,_Hlate,Hcoverage,Hsquare,Hmixed,Hconstant,
    Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_covered_target_susceptibility_along
      Atarget hAtarget Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hsaving:0 < actualSlowWindowExponent m delta/256:=
    div_pos (actualSlowWindowExponent_pos hm hdelta hroom) (by norm_num)
  have hT:0 < T:=hTemp.trans_le (sub_le_self T hepsilon)
  have hxs n:(M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hpair (Cmass : ℝ) (hCm : 0 ≤ Cmass) (degree : ℕ) (hd : 0 < degree):=
    actual_inherited_square_resource_pair_budget_of_actual_pair_producers_along degree hd
      hm hdelta hroom hcl hcu hAz hC0 hCt hT.le hCf Cmass hCm
      dim hdim M W hxs hWlim Hsource w (Hsquare (degree-1))
  have Hsharp:=eventually_actual_sharp_star_inherited_endpoint_second_along
    hm hdelta hC0 hCf dim hdim M W hcanonical hWlim w Hsource hw
  have Htotal:=actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  have Happrox (Cmass : ℝ) (hCm : 0 ≤ Cmass):=
    exists_actual_same_star_initial_residual_approx_along hm hcu hAz hC0 hT.le hTemp hsaving Cmass
      dim hdim M W hxs hWlim (Htotal.mono fun _ h=>h.1) (Htotal.mono fun _ h=>h.2)
      w hw (Hpair Cmass hCm)
  exact ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hcoverage,Hsquare,Hmixed,Hsharp,Hconstant,
    Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
