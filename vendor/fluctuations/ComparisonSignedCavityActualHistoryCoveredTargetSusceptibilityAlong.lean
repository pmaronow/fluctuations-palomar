module

public import ComparisonSignedCavityActualHistoryLateHalfSusceptibilityAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_covered_target_susceptibility_along
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
    ∃cK : ℝ,0 < cK ∧∃Cf : ℝ,0≤Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cwindow : ℝ,0 < Cwindow ∧∃w : ℕ → ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) (Atarget+1) Cwindow (w n)) ∧
      (∀ᶠn in atTop,(calibratedBandStart cu Az+2*(Atarget+1))*W n < (w n).star.val) ∧
      (∀ᶠn in atTop,Atarget*(M n).xs < (w n).star.val) ∧
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
  have hL : 0 < Atarget+1:=by linarith
  obtain ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hlate,Hsquare,Hmixed,Hconstant,Hcuts⟩:=
    exists_actual_selected_bad_history_later_half_susceptibility_along
      Rmacro Cx hmacro hRhalf hCx
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have Hcoverage : ∀ᶠn in atTop,Atarget*(M n).xs < (w n).star.val:=by
    have ha:=calibrated_band_start_pos hcu hAz
    filter_upwards [Hlate] with n hn
    have hx : (M n).xs ≤ W n:=by
      rw [hcanonical]
      exact (M n).canonical_direct_test_band_ge_scale
    have hW : 0 ≤ W n:=(M n).hxs.le.trans hx
    have H1:=mul_le_mul_of_nonneg_left hx hAtarget
    have H2:=mul_le_mul_of_nonneg_right
      (show Atarget ≤ calibratedBandStart cu Az+2*(Atarget+1) by linarith) hW
    exact (H1.trans H2).trans_lt hn
  exact ⟨cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hlate,Hcoverage,Hsquare,Hmixed,Hconstant,Hcuts⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
