module

public import ComparisonSignedCavityActualConstantSourceChildrenLevelsAlong
public import ComparisonSignedCavityActualConstantSourceChildrenFrozenAlong
public import ComparisonSignedCavityActualHistoryFourNumericInputsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem exists_actual_selected_bad_history_constant_source_four_inputs_along
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
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    let saving:=actualSlowWindowExponent m delta/256
    let sharpSaving:=actualMassSavingExponent m delta/32
    0<saving ∧ 0<sharpSaving ∧∃cK : ℝ,0<cK ∧
      (∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T) ∧ (M n).h 0=0) ∧
      ∃Cf : ℝ,0≤Cf ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∃Cs : ℝ,0<Cs ∧∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) ∧
      (∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNetAlong p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) ∧
      (∀degree : ℕ,0<degree→
        ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree 1 saving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenPairLevelSavingAlong depth saving sharpSaving M W w) ∧
      (∀depth : ℕ,ActualOriginalConstantSourceChildrenFrozenLevelSavingAlong depth saving M W w) ∧
      ActualOriginalConstantSourceChildrenFrozenSavingAlong saving M W w ∧
      ∃threshold : ℕ,0<threshold ∧∃terminalSaving : ℝ,0<terminalSaving ∧
        ∀depth : ℕ,threshold≤depth→
          ActualOriginalConstantSourceChildrenFourTerminalSavingAlong depth terminalSaving M W w := by
  obtain ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,Cs,hCs,w,hw,HK,Hsquare,Hmixed,
    _Hsharp,_Hinitial,_HinitialFrozen,_HinitialPair,Hconstant,HconstantPair,HconstantFrozen,
    _HinitialTerminal,HconstantTerminal,_Hbond⟩:=
    exists_actual_selected_bad_history_four_numeric_inputs_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hL hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hxs n : (M n).xs≤W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Htotal' := Htotal.mono (fun _ hn=>hn.1)
  have Hroot := Htotal.mono (fun _ hn=>hn.2)
  refine ⟨hs,hsharp,cK,hcK,Htotal,Cf,hCf,Hsource,Cs,hCs,w,hw,HK,Hsquare,Hmixed,
    fun degree hd=>(Hconstant degree hd).1,?_,?_,?_,?_⟩
  · intro depth
    exact (HconstantPair 1 depth 3 (by omega)).source_children hxs Htotal'
  · intro depth
    exact (HconstantFrozen 1 depth 3).source_children Htotal'
  · exact actual_inherited_constant_source_children_frozen_saving_of_pair_budget_along
      hm hC0 (by linarith) (by norm_num : (1:ℝ)≤1) dim hdim M W hxs Htotal' Hroot w
      (Hconstant 1 (by norm_num)).1
  · obtain ⟨threshold,hthreshold,saving,hsaving,Hterm⟩:=HconstantTerminal 3
    exact ⟨threshold,hthreshold,saving,hsaving,fun depth hd=>(Hterm depth hd).source_children Htotal'⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
