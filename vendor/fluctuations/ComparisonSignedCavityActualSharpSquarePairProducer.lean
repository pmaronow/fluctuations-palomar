module

public import ComparisonSignedCavityActualSharpStarAllOrder
public import ComparisonSignedCavityActualSquareResourcePairProducer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

theorem exists_actual_bare_sharp_square_resource_pair_budget_sequence
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
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n)) ∧
      (∀p : ℕ,ActualOriginalSquareStarMomentOnEveryFinalNet p saving M W w) ∧
      ∀degree : ℕ,0 < degree→∃A : ℝ,1≤A ∧
        ActualSquareResourcePairBudgetOnEveryFinalNet degree A saving Cmass M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,H,_⟩:=exists_actual_bare_sharp_native_star_on_every_final_net
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  have hxs n : (M n).xs≤W n := by
    rw [hcanonical]
    exact le_max_left _ _
  have hsite : actualSlowWindowExponent m delta/128 < (5:ℝ)/6+m := by
    have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
    linarith
  have Hsquare (p : ℕ) : ActualOriginalSquareStarMomentOnEveryFinalNet p
      (actualSlowWindowExponent m delta/256) M W w := by
    have HG:=actual_native_star_every_final_net_to_square p hcl hAz hC0 hs hsite
      M W hxs hWlim hb hh w (H p)
    simpa only [show (actualSlowWindowExponent m delta/128)/2=
      actualSlowWindowExponent m delta/256 by ring] using HG
  refine ⟨by linarith,Cs,hCs,w,hw,Hsquare,?_⟩
  intro degree hd
  exact actual_square_resource_pair_budget_of_actual_pair_producers degree hd
    hm hdelta hroom hcl hcu hAz hC0 hCt hTemp.le Cmass hCm
    M W hxs hWlim hb hh w (Hsquare (degree-1))

end OAI.SKFluctuations.LaplaceWindowFormalization
