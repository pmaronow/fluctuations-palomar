module

public import ComparisonActualHighWallSquarePairRetainedAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem actual_high_wall_square_pair_budgets_from_all_order_star_along
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hsaving : 0 < saving)
    (hsite : saving < (5:ℝ)/6+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (Hstar : ∀p : ℕ,∃Craw : ℝ,0 < Craw ∧ ActualHighWallStarOrderSavingAlong p Craw saving
      dim M (fun n=>(M n).data.d) w) :
    ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualHighWallSquareResourcePairBudgetOnRetainedMasterAlong degree A (saving/2)
        Cmass dim M w := by
  intro degree hd
  obtain ⟨Craw,_,Horder⟩:=Hstar (degree-1)
  have Hsquare:=actual_high_wall_original_square_star_on_retained_master_along (degree-1)
    hC0 hsaving hsite dim hdim M (fun n=>(M n).data.d)
    (fun n=>by rw [hfixed n]) hWlim w Horder
  exact actual_high_wall_square_resource_pair_budget_of_actual_square_star_along
    degree hd hm hdelta hroom hcl hcu hAz hC0 hCt Cmass hCm dim hdim M hfixed w Hsquare

theorem exists_actual_high_wall_square_resource_pair_budget_sequence_along
    {m delta cl cu Az C0 Ct D Bclock T0 L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT0 : 0 < T0) (hL : 0 < L) (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hWlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (hT : ∀n,T0 ≤ (M n).data.T) :
    let saving:=actualSlowWindowExponent m delta/128
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
        (M n) ((M n).data.d) L Cs (w n)) ∧
      ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
        ActualHighWallSquareResourcePairBudgetOnRetainedMasterAlong degree A saving
          Cmass dim M w := by
  have hc:=actualSlowWindowExponent_pos hm hdelta hroom
  have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
  have hsite : actualSlowWindowExponent m delta/64 < (5:ℝ)/6+m:=by linarith
  obtain ⟨Cs,hCs,w,hw,Hstar⟩:=exists_actual_high_wall_calibrated_all_order_star_sequence_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hT0 hL dim hdim M hfixed hWlim hsRatio hT
  refine ⟨by positivity,Cs,hCs,w,hw,?_⟩
  have H:=actual_high_wall_square_pair_budgets_from_all_order_star_along
    hm hdelta hroom hcl hcu hAz hC0 hCt Cmass hCm (by positivity) hsite
    dim hdim M hfixed hWlim w Hstar
  simpa only [show (actualSlowWindowExponent m delta/64)/2=
    actualSlowWindowExponent m delta/128 by ring] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
