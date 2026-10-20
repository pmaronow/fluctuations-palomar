module

public import ComparisonSignedCavityActualHistoryMomentsAtSharpWindowAlong
public import ComparisonSignedCavityActualHistoryFourNumericInputsAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 24000000

theorem actual_selected_bad_history_four_numeric_inputs_at_sharp_window_along
    {m delta cl cu Az C0 Ct D Bclock T L Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0 < saving ∧ 0 < sharpSaving ∧ ∃cK : ℝ,0 < cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0 ≤ Cf ∧
      (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
        (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
        (∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
        (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
        (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
        ActualSharpEndpointStarSecondMomentOnEveryFinalNetAlong sharpSaving M W w ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀degree : ℕ,0 < degree →
          ∃A : ℝ,1 ≤ A ∧
            ActualSquareResourcePairBudgetOnEveryFinalNetAlong degree A saving Cmass M W w ∧
            ActualOriginalFreshPairResourceSavingOnEveryFinalNetAlong
              degree A saving sharpSaving Cmass M W w ∧
            ActualOriginalFourPairContrastSavingOnEveryFinalNetAlong
              degree A saving sharpSaving Cmass M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀depth : ℕ,
          ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass → ∀k0 depth r : ℕ,
          ActualOriginalFourInitialPairForestSavingAlong k0 depth r saving sharpSaving Cmass M W w) ∧
        (∀degree : ℕ,0 < degree →
          ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w ∧
          ActualOriginalConstantFreshPairSavingOnEveryFinalNetAlong degree saving sharpSaving M W w ∧
          ActualOriginalConstantFourPairContrastSavingOnEveryFinalNetAlong degree saving sharpSaving M W w) ∧
        (∀k0 depth r : ℕ,0 < k0+depth →
          ActualOriginalConstantFourPairForestSavingAlong k0 depth r saving sharpSaving M W w) ∧
        (∀k0 depth r : ℕ,ActualOriginalFourConstantFrozenChildLevelSavingAlong
          k0 depth r saving M W w) ∧
        (∀Cmass : ℝ,0 ≤ Cmass →∃threshold : ℕ,0 < threshold ∧∃terminalSaving : ℝ,
          0 < terminalSaving ∧∀depth : ℕ,threshold ≤ depth→
            ActualOriginalContinuumNaturalCenteredFourGTerminalSavingAlong depth terminalSaving Cmass M W w) ∧
        (∀r : ℕ,∃threshold : ℕ,0 < threshold ∧∃terminalSaving : ℝ,
          0 < terminalSaving ∧∀depth : ℕ,threshold ≤ depth→
            ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong r depth terminalSaving M W w) ∧
        ∃Cb : ℝ,0 < Cb ∧∀ᶠn in atTop,∀(as : List PositiveMass)
          (_ho : MassOrdered 0 as),(w n).star∈as→
          ∀U : ℕ,retainedMassPrefixIndex (w n).star.val as < U→U ≤ as.length→
            let star:=retainedMassPrefixIndex (w n).star.val as
            let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
            let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
            |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤
              |(T-epsilon)*chi^2-1|+Cb*(W n)^2 := by
  obtain ⟨hs,hsharp,Cf,hCf,Hsource,hw,Hsquare,Hmixed,Hsharp,Hpair,Hconstant⟩:=
    actual_selected_bad_history_sharp_fresh_pair_feedback_at_sharp_window_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare Cs hCs w hw
  let cK:=3*(T-epsilon)*(starMassBandConstant cu Az/cu)/8
  have hcK : 0 < cK := by
    dsimp only [cK]
    exact div_pos (mul_pos (mul_pos (by norm_num) hTemp)
      (div_pos (star_mass_band_constant_pos hcu hAz) hcu)) (by norm_num)
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M
    epsilon shell hepsilon hb hh Hhistory
  have HK : ∀ᶠn in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    filter_upwards [hw] with n hn
    obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,Hclock,_⟩:=hn.1
    exact Hclock
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,hw,HK,
    Hsquare,Hmixed,Hsharp,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro Cmass hCm degree hd
    obtain ⟨A,hA,HP,HF⟩:=Hpair Cmass hCm degree hd
    exact ⟨A,hA,HP,HF,actual_original_four_pair_contrast_saving_of_fresh_feedback_along degree A M W w HF⟩
  · intro Cmass hCm depth
    obtain ⟨A,hA,HP,_⟩:=Hpair Cmass hCm (depth+2) (by omega)
    exact actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
      hm hC0 (by linarith) hs hcK depth hA Cmass dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK HP
  · intro Cmass hCm k0 depth r
    obtain ⟨A,hA,_,HF⟩:=Hpair Cmass hCm (1+k0+depth) (by omega)
    exact actual_inherited_four_initial_pair_forest_saving_along (by linarith) hsharp hcK
      k0 depth r hA Cmass dim hdim M W hxs (Htotal.mono (fun _ hn=>hn.1)) w HK
      (actual_original_four_pair_contrast_saving_of_fresh_feedback_along (1+k0+depth) A M W w HF)
  · intro degree hd
    obtain ⟨HP,HF⟩:=Hconstant degree hd
    exact ⟨HP,HF,actual_original_constant_four_pair_contrast_saving_of_fresh_feedback_along degree M W w HF⟩
  · intro k0 depth r hd
    exact actual_inherited_constant_four_pair_forest_saving_along (by linarith) hsharp hcK
      k0 depth r dim hdim M W hxs (Htotal.mono (fun _ hn=>hn.1)) w HK
      (actual_original_constant_four_pair_contrast_saving_of_fresh_feedback_along (k0+depth) M W w
        (Hconstant (k0+depth) hd).2)

  · intro k0 depth r
    exact actual_inherited_four_constant_frozen_child_level_saving_of_pair_budget_along
      hm hC0 (by linarith) hcK k0 depth r (by norm_num) dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) (Htotal.mono (fun _ hn=>hn.2)) w HK
      (Hconstant (k0+depth+1) (by omega)).1
  · intro Cmass hCm
    exact exists_actual_sharp_same_star_natural_centered_four_G_terminal_along
      hm hcu hAz hC0 (by linarith) hTemp hs Cmass dim hdim M W hxs hWlim
      (Htotal.mono (fun _ hn=>hn.1)) w hw (fun degree hd=>by
        obtain ⟨A,hA,HP,_⟩:=Hpair Cmass hCm degree hd
        exact ⟨A,hA,HP⟩)
  · intro r
    exact exists_actual_sharp_same_star_generated_constant_four_G_terminal_along
      hm hcu hAz hC0 (by linarith) hTemp hs r dim hdim M W hxs
      (Htotal.mono (fun _ hn=>hn.1)) w hw (fun degree hd=>(Hconstant degree hd).1)
  · exact actual_selected_bad_history_susceptibility_coefficient_along
      hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim w hw

end OAI.SKFluctuations.LaplaceWindowFormalization
