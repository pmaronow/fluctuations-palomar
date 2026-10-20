module

public import ComparisonSignedCavityActualHistoryClosedTargetInitialJointAlong
public import ComparisonSignedCavityActualCalibratedInitialPairFeedbackAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_closed_initial_feedback_along
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
    0 < saving ∧∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cwindow (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong
        (actualMassSavingExponent m delta/32) M W w ∧
      (∀degree : ℕ,0 < degree → ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
        ∃A : ℝ,1 ≤ A ∧ ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∃thresholdI : ℕ,0 < thresholdI ∧ ∃savingI : ℝ,0 < savingI ∧
        ∀depth : ℕ,thresholdI ≤ depth → ActualTargetInitialResidualApproxAlong depth savingI Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀depth : ℕ,
        ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w) ∧
      (∀Cmass : ℝ,0 ≤ Cmass → ∀k0 depth r : ℕ,
        ActualOriginalFourInitialPairForestSavingAlong k0 depth r saving
          (actualMassSavingExponent m delta/32) Cmass M W w) ∧
      ∃Ku Kv cFirst cKcut : ℝ,1 < Ku ∧1≤Kv ∧0 < cFirst ∧2*cu*(Az+1)≤cFirst ∧0 < cKcut ∧
      ∃high outer : ℕ → PositiveMass,
      (∀n,(high n).val=Ku*W n ∧(outer n).val=(Ku+1)*W n) ∧
      (∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
        (high n) (outer n) (Kv*W n) cFirst cKcut (Ku+1) Rmacro Cx) ∧
      ∃threshold : ℕ,0 < threshold ∧∀depth : ℕ,threshold≤depth →
        ∃C : ℝ,0 < C ∧(∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses Lnet,u∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us → high n∈us → outer n∈us →
        (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) → ∀ᶠj in atTop,
          let as:=finiteCutMasses us j
          let star:=retainedMassPrefixIndex (w n).star.val as
          let U:=retainedMassPrefixIndex (high n).val as
          ∃_hs : star < U,∃_hU : U≤as.length,
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |(T-epsilon)*chi^2-1|≤C*(W n)^2 ∧
          |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2|≤C*(W n)^2) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀feedbackDepth : ℕ,∃err : ℕ→ℝ,
          (∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧
          ActualInitialPairFeedbackResidualOnStrongCutsAlong feedbackDepth T cKcut Cmass err M W w high outer) := by
  obtain ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hsharp,Hconstant,
    Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,hcKcut,high,outer,Hvalues,Hstrong,
    threshold,hthreshold,Hbootstrap⟩:=exists_actual_selected_bad_history_closed_target_initial_residual_joint_along
      Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hT : 0 < T:=hTemp.trans_le (sub_le_self T hepsilon)
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Htotal:=actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  have Hclock:=Hstrong.mono (fun _ hn=>hn.clock_star)
  have hsharp : 0 < actualMassSavingExponent m delta/32:=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have Hnum (Cmass : ℝ) (hCm : 0 ≤ Cmass):=
    actual_same_star_initial_four_numeric_inputs_along hm hC0 hT.le hsaving hsharp hcKcut
      Cmass dim hdim M W hxs (Htotal.mono fun _ hn=>hn.1) (Htotal.mono fun _ hn=>hn.2)
      w Hclock (Hpair Cmass hCm) Hsharp
  refine ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hsquare,Hmixed,Hsharp,Hconstant,
    Hpair,Happrox,(fun Cmass hCm=>(Hnum Cmass hCm).2.1),
    (fun Cmass hCm=>(Hnum Cmass hCm).2.2),Ku,Kv,cFirst,cKcut,hKu,hKv,hFirst,hFirstLower,
    hcKcut,high,outer,Hvalues,Hstrong,threshold,hthreshold,?_⟩
  intro depth hdepth
  obtain ⟨C,hC,HC⟩:=Hbootstrap depth hdepth
  refine ⟨C,hC,HC,?_⟩
  have HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong C M W w high outer:=by
    filter_upwards [HC] with n hn
    intro Lnet us hus hret hmesh hstar hhigh houter hnodes
    filter_upwards [hn Lnet us hus hret hmesh hstar hhigh houter hnodes] with j hj
    obtain ⟨_,_,_,HJ⟩:=hj
    exact HJ
  intro Cmass hCm feedbackDepth
  exact actual_calibrated_initial_pair_feedback_residual_along feedbackDepth hsaving.le hsharp hcKcut hC.le
    hdim M W (fun n=>Kv*W n) hxs w high outer
    (Hstrong.mono fun _ hn=>hn.toActualSharpSourceCutGeometry) HJ
    (fun d=>(Hnum Cmass hCm).2.2 0 d 2)

end OAI.SKFluctuations.LaplaceWindowFormalization
