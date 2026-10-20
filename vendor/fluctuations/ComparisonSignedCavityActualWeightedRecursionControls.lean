module

public import ComparisonSignedCavityActualWeightedFrozenFrontier
public import ComparisonSignedCavityActualSquareWeightedGDecay

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem exists_actual_bare_sharp_weighted_recursion_terminal_controls
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hTemp : 0 < Temp) (hL : 0 < Lwin) (hCcal : 1≤Ccal)
    (Cmass : ℝ) (hCm : 0≤Cmass)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2≤Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n)) ∧
      (∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
        ∀Cbeta : ℝ,0≤Cbeta→∀branches : NativeActualWeightedBranches,
        ∀L : ℕ,(∀b∈branches,b.2.length≤L)→
        ∀increment : ℕ,0 < increment→
          (∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)→
        ∀depth : ℕ,threshold≤depth→
          ActualSquareInitialWeightedGFrontierDecay Cbeta branches depth saving Cmass M W w) ∧
      (∀Cbeta : ℝ,0≤Cbeta→∀branches : NativeActualWeightedBranches,
        ∀L : ℕ,(∀b∈branches,b.2.length≤L)→
        ∀increment : ℕ,(∀b∈branches,nativeActualExpansionMarkedCount b.2=increment)→
        ∀depth : ℕ,ActualOriginalWeightedFrozenFrontierSaving Cbeta branches depth Cmass M W w) := by
  obtain ⟨hs,Cs,hCs,w,hw,_,Hp⟩:=exists_actual_bare_sharp_square_resource_pair_budget_sequence
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hL hCcal Cmass hCm
    M W hcanonical hWlim hcompare hb hh
  have hxs : ∀n,(M n).xs≤W n:=fun n=>by rw [hcanonical];exact le_max_left _ _
  have Hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n) :=
    hw.mono (fun _ hn=>hn.1)
  refine ⟨Cs,hCs,w,hw,?_,?_⟩
  · exact actual_square_weighted_g_frontier_decay_of_pair_producers
      hm hcl hcu hAz hC0 hTemp hs Cmass M W hxs hWlim hb hh Cs w Hw Hp
  · intro Cbeta hCbeta branches L hlen increment hinc depth
    obtain ⟨A,hA,HA⟩:=Hp (1+depth*increment) (by omega)
    exact actual_original_weighted_frozen_frontier_saving_of_pair_budget
      hm hcl hcu hAz hC0 hTemp hs Cbeta hCbeta branches L hlen increment hinc depth hA Cmass
      M W hxs hWlim hb hh Cs w Hw HA

end OAI.SKFluctuations.LaplaceWindowFormalization
